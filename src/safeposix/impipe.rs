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
use crate::fdtables::FDTableEntry;

use std::sync::{Arc, Mutex, Condvar};
use std::sync::atomic::{AtomicBool, Ordering};
use rb::*;
use std::cmp::min;
use std::slice;
use std::thread::yield_now;
use libc::{O_RDONLY, O_WRONLY, iovec};
use std::ffi::CString;
pub use std::sync::LazyLock;
pub use dashmap::{mapref::entry::Entry, DashMap, DashSet};
use crate::interface::GenSockaddr;

// boolean to enable IMPIPE/IMSOCK use in syscalls
pub const USE_IM_PIPE: bool = true;

// setting max number of pipes/sockets to 1024
const MAXPIPE: u64 = 1024;

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

// various sockethandle connection states for IMSockets
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ConnState {
    NOTCONNECTED,
    DISCONNECTED,
    CONNECTED,
    CONNRDONLY,
    CONNWRONLY,
    LISTEN,
    INPROGRESS,
}

pub enum IPCTableEntry {
    Pipe(PipeEntry),
    DomainSocket(SocketHandle),
}

pub struct PipeEntry {
    pub pipe: Arc<IMPipe>,
}

//This structure contains all socket-associated data that is not held in the fd
pub struct SocketHandle {
    pub domain: i32,
    pub socktype: i32,
    pub protocol: i32,
    pub mode: i32,
    pub socket_options: i32,
    pub tcp_options: i32,
    pub state: ConnState,
    pub localaddr: Option<GenSockaddr>,
    pub remoteaddr: Option<GenSockaddr>,
    pub sendpipe: Option<Arc<IMPipe>>,
    pub receivepipe: Option<Arc<IMPipe>>
}

// Table for ipc structures, contains either a pipe entry or domain socket handle
pub static IPC_TABLE: LazyLock<DashMap<u64, IPCTableEntry>> = 
    LazyLock::new(|| 
        DashMap::new()
);

// Doman Socket Connection Data Structures

pub static DS_CONNECTION_TABLE: LazyLock<DashMap<CString, DSConnTableEntry>> = 
    LazyLock::new(|| 
        DashMap::new()
);

pub static BOUND_SOCKETS: LazyLock<DashSet<CString>> = 
LazyLock::new(|| 
    DashSet::new()
);

// lazily search through IPC_TABLE for next available entry and insert pipe
pub fn insert_next_pipe(pipe: Arc<IMPipe>) -> Option<u64> {

    let ipcentry = IPCTableEntry::Pipe(PipeEntry{pipe});

    for ipcnum in 0..MAXPIPE {
        if let Entry::Vacant(v) = IPC_TABLE.entry(ipcnum) {
            v.insert(ipcentry);
            return Some(ipcnum);
        }
    }

    return None;
}

// lazily search through IPC_TABLE for next available entry and insert sockethandle
pub fn insert_next_sockhandle(domain: i32, socktype: i32, protocol: i32, mode: i32) -> Option<u64> {

    let ipcentry = IPCTableEntry::DomainSocket(SocketHandle{domain, socktype, protocol, mode: mode, socket_options: 0, tcp_options: 0, state: ConnState::NOTCONNECTED, localaddr: None, remoteaddr: None, sendpipe: None, receivepipe: None});

    for ipcnum in 0..MAXPIPE {
        if let Entry::Vacant(v) = IPC_TABLE.entry(ipcnum) {
            v.insert(ipcentry);
            return Some(ipcnum);
        }
    }

    return None;
}

// Conditional variable struct to be used for making blocking socket connections
// wraps a lock and condvar for an easy api to wait and broadcast
// this variable is created on connect and is signaled to be released upon an accept call for the matching socket
pub struct ConnCondVar {
    lock: Arc<Mutex<i32>>,
    cv: Condvar,
}

impl ConnCondVar {
    pub fn new() -> Self {
        Self {
            lock: Arc::new(Mutex::new(0)),
            cv: Condvar::new(),
        }
    }

    pub fn wait(&self) {
        let mut guard = self.lock.lock().unwrap();
        *guard += 1;
        let _result = self.cv.wait(guard);
    }

    pub fn broadcast(&self) -> bool {
        let guard = self.lock.lock().unwrap();
        if *guard == 1 {
            self.cv.notify_all();
            return true;
        } else {
            return false;
        }
    }
}

// connection table structure for connect/accept of IMSockets
// we give this structure the connecting sockets address
// two pipes for sending and receiving, that will be matched with the accepted socket
// and the above CV for blocking until accepted
pub struct DSConnTableEntry {
    pub sockaddr: GenSockaddr,
    pub receive_pipe: Arc<IMPipe>,
    pub send_pipe: Arc<IMPipe>,
    pub cond_var: Option<Arc<ConnCondVar>>,
}

impl DSConnTableEntry {
    pub fn get_cond_var(&self) -> Option<&Arc<ConnCondVar>> {
        self.cond_var.as_ref()
    }
    pub fn get_sockaddr(&self) -> &GenSockaddr {
        &self.sockaddr
    }
    pub fn get_send_pipe(&self) -> &Arc<IMPipe> {
        &self.send_pipe
    }
    pub fn get_receive_pipe(&self) -> &Arc<IMPipe> {
        &self.receive_pipe
    }
}

// close routine to be called when last pipe reference to an fd is called
// will set readers/writers closed if the fd is last reference to either
// or remove the entry from the IPC table if both sides are closed
pub fn close_im_pipe(impipe_entry:FDTableEntry, count: u64) {
    if count > 0 { return; }

    if let IPCTableEntry::Pipe(ref pipe_entry) = *IPC_TABLE.get(&impipe_entry.underfd).unwrap(){

        if impipe_entry.perfdinfo as i32 & O_RDONLY != 0 { 
            pipe_entry.pipe.set_readers_closed();
            if pipe_entry.pipe.check_writers_closed() {
                IPC_TABLE.remove(&impipe_entry.underfd);
            }
        } else if impipe_entry.perfdinfo as i32 & O_WRONLY != 0 { 
            pipe_entry.pipe.set_writers_closed();
            if pipe_entry.pipe.check_readers_closed() {
                IPC_TABLE.remove(&impipe_entry.underfd);
            }
        }
    }
}

// close routine to be called when last reference to socket fd is called
// will set writers closed on send pipe or readers closed on receive pipe
// if the other side is already closed it will remove the sockethandle from the ipc table
pub fn close_im_socket(imsock_entry:FDTableEntry, count: u64) {
    if count > 0 { return; }

    if let IPCTableEntry::DomainSocket(ref sock_entry) = *IPC_TABLE.get(&imsock_entry.underfd).unwrap(){

        if let Some(sendpipe) = &sock_entry.sendpipe {
            sendpipe.set_writers_closed();
            if sendpipe.check_readers_closed() {
                IPC_TABLE.remove(&imsock_entry.underfd);
            }
        } else if let Some(receivepipe) = &sock_entry.receivepipe {
            receivepipe.set_readers_closed();
            if receivepipe.check_writers_closed() {
                IPC_TABLE.remove(&imsock_entry.underfd);
            }
        }
    }
}