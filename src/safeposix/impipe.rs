#![allow(dead_code)]


// Author: Nicholas Renner

//! In-Memory Pipe Imlpementation for pairing with RawPOSIX
//!
//! ## Pipe Module
//!
//! This module provides a method for in memory iPC between cages and is able to
//! replicate both pipes and Unix domain sockets.
//!
//! Linux pipes are implemented as a circular buffer of 16 pages (4096 bytes
//! each). Instead for RustPOSIX we implement the buffer as a circular
//! buffer for the sum of bytes in those pages.
//!
//! This implementation is also used internally by RustPOSIX to approximate Unix
//! sockets by allocating two of these pipes bi-directionally.
//!
//! We expose an API allowing to read and write to the pipe as well as check if
//! pipe descriptors are reading for reading and writing via select/poll
///
/// To learn more about pipes
/// [pipe(7)](https://man7.org/linux/man-pages/man7/pipe.7.html)
use crate::safeposix::cage::*;

use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicBool, Ordering};
use rb::*;
use std::cmp::min;
use std::slice;
use std::thread::yield_now;
use libc::iovec;

// lets define a few constants for the standard size of a Linux page and errnos
const PAGE_SIZE: usize = 4096;
const EAGAIN: i32 = 11;
const EPIPE: i32 = 32;

/// # Description
/// In-memory pipe struct of given size which contains a reference to the circular buffer, and methods to determine if an end of the pipe is closed
/// end
#[derive(Clone)]
pub struct IMPipe {
    buffer: Arc<Mutex<SpscRb<u8>>>,
    closed_readers: Arc<AtomicBool>,
    closed_writers: Arc<AtomicBool>,
    size: usize,
}

impl IMPipe {
    /// # Description
    /// Creates an in-memory pipe object of specified size.
    /// The size provided is either a constant for a pipe (65,536 bytes) or a
    /// domain socket (212,992 bytes)
    ///
    /// # Arguments
    ///
    /// * `size` - Size of the iPC construct in bytes (either pipe or Unix
    ///   socket)
    ///
    /// # Returns
    ///
    /// InMemoryPipe object
    pub fn new_with_capacity(size: usize) -> IMPipe {
        let rb = SpscRb::<u8>::new(size);

        IMPipe {
            buffer: Arc::new(Mutex::new(rb)),
            closed_readers: Arc::new(AtomicBool::new(false)),
            closed_writers: Arc::new(AtomicBool::new(false)),
            size: size,
        }
    }

    /// Setter for closed readers
    /// used to determine EOF
    pub fn set_readers_closed(&self) {
        self.closed_readers.store(true, Ordering::Relaxed)
    }

    /// Setter for closed writers
    /// used to determine EPIPE
    pub fn set_writers_closed(&self) {
        self.closed_writers.store(true, Ordering::Relaxed)
    }

    /// Internal getter for checking closed read end
    ///
    /// Returns if pipe read end is closed
    fn check_readers_closed(&self) -> bool {
        self.closed_readers.load(Ordering::Relaxed)
    }

    /// Internal getter for checking closed write end
    ///
    /// Returns if pipe write end is closed
    fn check_writers_closed(&self) -> bool {
        self.closed_writers.load(Ordering::Relaxed)
    }


    /// # Description
    /// Checks if pipe is currently ready for reading, used by select/poll etc.
    /// A pipe descriptor is ready if there is anything in the pipe or the write end is closed.
    ///
    /// # Returns
    ///
    /// True if descriptor is ready for reading, false if it will block
    pub fn check_select_read(&self) -> bool {
        let buffer = self.buffer.lock().unwrap();
        let pipe_space = buffer.count();

        return (pipe_space > 0) || self.check_writers_closed();
    }

    /// # Description
    /// Checks if pipe is currently ready for writing, used by select/poll etc.
    /// A pipe descriptor is ready for writing if there is more than a page
    /// (4096 bytes) of room in the pipe or if the read end is closed
    ///
    /// # Returns
    ///
    /// True if descriptor is ready for writing, false if it will block
    pub fn check_select_write(&self) -> bool {
        let buffer = self.buffer.lock().unwrap();
        let pipe_space = buffer.slots_free();

        // Linux considers a pipe writeable if there is at least PAGE_SIZE (PIPE_BUF)
        // remaining space (4096 bytes)
        return pipe_space > PAGE_SIZE || self.check_readers_closed();
    }

    /// ### Description
    ///
    /// write_to_pipe writes a specified number of bytes starting at the given
    /// pointer to a circular buffer.
    ///
    /// ### Arguments
    ///
    /// write_to_pipe accepts three arguments:
    /// * `ptr` - a pointer to the data being written.
    /// * `length` - the amount of bytes to attempt to write
    /// * `nonblocking` - if this attempt to write is nonblocking
    ///
    /// ### Returns
    ///
    /// Upon successful completion, the amount of bytes written is returned.
    /// In case of a failure, an error is returned to the calling syscall.
    ///
    /// ### Errors
    ///
    /// * `EAGAIN` - Non-blocking is enabled and the write has failed to fully
    ///   complete.
    /// * `EPIPE` - An attempt to write to a pipe with all read references have
    ///   been closed.
    ///
    /// ### Panics
    ///
    /// A panic occurs if the provided pointer is null
    ///
    /// To learn more about pipes and the write syscall
    /// [pipe(7)](https://man7.org/linux/man-pages/man7/pipe.7.html)
    /// [write(2)](https://man7.org/linux/man-pages/man2/write.2.html)
    pub fn write_to_pipe(&self, ptr: *const u8, length: usize, nonblocking: bool) -> i32 {
        // unlikely but if we attempt to write nothing, return 0
        if length == 0 {
            return 0;
        }

        // convert the raw pointer into a slice to interface with the circular buffer
        let buf = unsafe {
            assert!(!ptr.is_null());
            slice::from_raw_parts(ptr, length)
        };

        let buffer = self.buffer.lock().unwrap();
        let write_end = buffer.producer();
        let mut bytes_written = 0;

        // Here we attempt to write the data to the pipe, looping until all bytes are
        // written or in non-blocking scenarios error with EAGAIN
        //
        // Here are the four different scenarios we encounter (via the pipe(7) manpage):
        //
        // O_NONBLOCK disabled, n <= PAGE_SIZE
        // All n bytes are written, write may block if
        // there is not room for n bytes to be written immediately

        // O_NONBLOCK enabled, n <= PAGE_SIZE
        // If there is room to write n bytes to the pipe, then
        // write succeeds immediately, writing all n bytes;
        // otherwise write fails, with errno set to EAGAIN.

        // O_NONBLOCK disabled, n > PAGE_SIZE
        // The write blocks until n bytes have been written.
        // Because Linux implements pipes as a buffer of pages, we need to wait until
        // a page worth of bytes is free in our buffer until we can write

        // O_NONBLOCK enabled, n > PAGE_SIZE
        // If the pipe is full, then write fails, with errno set to EAGAIN.
        // Otherwise, a "partial write" may occur returning the number of bytes written

        while bytes_written < length {
            if self.check_readers_closed() {
                // we send EPIPE here since all read ends are closed
                return syscall_error(Errno::EPIPE, "write", "Read end closed");
            }

            let remaining = buffer.slots_free();

            // we loop until either more than a page of bytes is free in the pipe
            // Linux technically writes a page per iteration here but its more efficient and
            // should be semantically equivalent to write more for why we wait
            if remaining < PAGE_SIZE {
                if nonblocking {
                    // for non-blocking if we have written a bit lets return how much we've written,
                    // otherwise we return EAGAIN
                    if bytes_written > 0 {
                        return bytes_written as i32;
                    } else {
                        return syscall_error(Errno::EAGAIN, "write", "File Descriptor would block");
                    }
                } else {
                    // we yield here on a non-writable pipe to let other threads continue more
                    // quickly
                    yield_now();
                    continue;
                }
            };

            // lets read the minimum of the specified amount or whatever space we have
            let bytes_to_write = min(length, bytes_written as usize + remaining);
            write_end.write(&buf[bytes_written..bytes_to_write]).unwrap();
            bytes_written = bytes_to_write;
        }

        // lets return the amount we've written to the pipe
        bytes_written as i32
    }

    /// ### Description
    ///
    /// write_vectored_to_pipe translates iovecs into a singular buffer so that
    /// write_to_pipe can write that data to a circular buffer.
    ///
    /// ### Arguments
    ///
    /// write_to_pipe accepts three arguments:
    /// * `ptr` - a pointer to an Iovec array.
    /// * `iovcnt` - the number of iovec indexes in the array
    /// * `nonblocking` - if this attempt to write is nonblocking
    ///
    /// ### Returns
    ///
    /// Upon successful completion, the amount of bytes written is returned via
    /// write_to_pipe. In case of a failure, an error is returned to the
    /// calling syscall.
    ///
    /// ### Errors
    ///
    /// * `EAGAIN` - Non-blocking is enabled and the write has failed to fully
    ///   complete (via write_to_pipe).
    /// * `EPIPE` - An attempt to write to a pipe when all read references have
    ///   been closed (via write_to_pipe).
    ///
    /// ### Panics
    ///
    /// A panic occurs if the provided pointer is null
    ///
    /// To learn more about pipes and the writev syscall
    /// [pipe(7)](https://man7.org/linux/man-pages/man7/pipe.7.html)
    /// [pipe(7)](https://man7.org/linux/man-pages/man2/writev.2.html)
    pub fn write_vectored_to_pipe(
        &self,
        ptr: *const iovec,
        iovcnt: i32,
        nonblocking: bool,
    ) -> i32 {
        // unlikely but if we attempt to write 0 iovecs, return 0
        if iovcnt == 0 {
            return 0;
        }

        let mut buf = Vec::new();
        let mut length = 0;

        // we're going to loop through the iovec array and combine the buffers into one
        // Rust slice so that we can use the write_to_pipe function, recording the
        // length this is hacky but is the best way to do this for now
        for _iov in 0..iovcnt {
            unsafe {
                assert!(!ptr.is_null());
                // lets convert this iovec into a Rust slice,
                // and then extend our combined buffer
                let iovec = *ptr;
                let iovbuf = slice::from_raw_parts(iovec.iov_base as *const u8, iovec.iov_len);
                buf.extend_from_slice(iovbuf);
                length = length + iovec.iov_len
            };
        }

        // now that we have a single buffer we can use the usual write to pipe function
        self.write_to_pipe(buf.as_ptr(), length, nonblocking)
    }

    /// ### Description
    ///
    /// read_from_pipe reads a specified number of bytes from the circular
    /// buffer to a given pointer.
    ///
    /// ### Arguments
    ///
    /// write_to_pipe accepts three arguments:
    /// * `ptr` - a pointer to the buffer being read to.
    /// * `length` - the amount of bytes to attempt to read
    /// * `nonblocking` - if this attempt to read is nonblocking
    ///
    /// ### Returns
    ///
    /// Upon successful completion, the amount of bytes read is returned.
    /// In case of a failure, an error is returned to the calling syscall.
    ///
    /// ### Errors
    ///
    /// * `EAGAIN` - A non-blocking  read is attempted without EOF being reached
    ///   but there is no data in the pipe.
    ///
    /// ### Panics
    ///
    /// A panic occurs if the provided pointer is null
    ///
    /// To learn more about pipes and the read syscall
    /// [read(2))](https://man7.org/linux/man-pages/man2/read.2.html)
    pub fn read_from_pipe(&self, ptr: *mut u8, length: usize, nonblocking: bool) -> i32 {
        // unlikely but if we attempt to read nothing, return 0
        if length == 0 {
            return 0;
        }

        // convert the raw pointer into a slice to interface with the circular buffer
        let buf = unsafe {
            assert!(!ptr.is_null());
            slice::from_raw_parts_mut(ptr, length)
        };

        let buffer = self.buffer.lock().unwrap();
        let read_end = buffer.consumer();
        let mut pipe_space = buffer.count();

        if nonblocking && (pipe_space == 0) {
            // if the descriptor is non-blocking and theres nothing in the pipe we either:
            // return 0 if the EOF is reached (zero write references)
            // or return EAGAIN due to the O_NONBLOCK flag
            if self.check_writers_closed() {
                return 0;
            }
            return syscall_error(Errno::EAGAIN, "read", "File Descriptor would block");
        }

        // wait for something to be in the pipe, but break on eof
        while pipe_space == 0 {
            // If write references are 0, we've reached EOF so return 0
            if self.check_writers_closed() {
                return 0;
            }

            // lets check again if were empty
            pipe_space = buffer.count();
            if pipe_space == 0 {
                // we yield here on an empty pipe to let other threads continue more quickly
                yield_now();
            }
        }

        // we've found something in the pipe
        // lets read the minimum of the specified amount or whatever is in the pipe
        let bytes_to_read = min(length, pipe_space);
        read_end.read(&mut buf[0..bytes_to_read]).unwrap();

        // return the amount we read
        bytes_to_read as i32
    }
}


// RawPOSIX specific datastructures
pub use std::sync::LazyLock;
pub use dashmap::{mapref::entry::Entry, DashMap};
pub const USE_IM_PIPE: bool = true;

const MAXPIPE: u64 = 1024;

pub struct PipeTableEntry {
    pub pipe: Arc<IMPipe>,
    pub blocking: bool,
    pub isreader: bool
}

pub static PIPE_TABLE: LazyLock<DashMap<u64, Arc<PipeTableEntry>>> = 
    LazyLock::new(|| 
        DashMap::new()
);

pub fn insert_next_pipe(pipe: Arc<IMPipe>, blocking: bool, isreader: bool) -> Option<u64> {

    let ptentry = PipeTableEntry{pipe, blocking, isreader};

    for pipeno in 0..MAXPIPE {
        if let Entry::Vacant(v) = PIPE_TABLE.entry(pipeno) {
            v.insert(Arc::new(ptentry));
            return Some(pipeno);
        }
    }

    return None;
}