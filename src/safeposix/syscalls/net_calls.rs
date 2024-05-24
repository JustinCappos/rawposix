#![allow(dead_code)]
// Network related system calls
// outlines and implements all of the networking system calls that are being emulated/faked in Lind

use super::net_constants::*;
use crate::{interface::FdSet, safeposix::cage::*};

use crate::example_grates::fdtable::*;

use libc::*;
use core::panic;
use std::{os::fd::RawFd, ptr};
use bit_set::BitSet;

/* A,W:
*   [Related Changes]
*    - Added some helper functions in fdtables repo
*
*   [Concern / TODO]
*    - Use functions in fdtalbes repo? --> treat fdtables as package?
*    - Type conversion?
*       1. For now I assume the user will use linux data structure when
*          they want to use libc functions, but for fd / fd_set they need to use our implementation..?
*    - Need to check parameter data type and libc function data type (eg: mut / not using, etc.)
*    - The socket_vector in socketpair() ...?
*    - Do the type conversion inside each syscall
*    - Error handling 
*    - cloexec in get_unused_virtual_fd()..?
*/

impl Cage {
    /* 
     *   Mapping a new virtual fd and kernel fd that libc::socket returned
     *   Then return virtual fd
     */
    pub fn socket_syscall(&self, domain: u64, socktype: u64, protocol: u64) -> u64 {
        let kernel_fd = unsafe { libc::socket(domain as i32, socktype as i32, protocol as i32) };
        /*
            get_unused_virtual_fd(cageid,realfd,is_cloexec,optionalinfo) -> Result<virtualfd, EMFILE>
        */
        return get_unused_virtual_fd(self.cageid, kernel_fd as u64, false, 0).unwrap();
    }

    /* 
     *   Get the kernel fd with provided virtual fd first
     *   bind() will return 0 when success and -1 when fail
     */
    pub fn bind_syscall(&self, virtual_fd: u64, addr: *const sockaddr, len: u64) -> i32 {
        /*
            translate_virtual_fd(cageid: u64, virtualfd: u64) -> Result<u64, threei::RetVal>
        */
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe { libc::bind(kernel_fd as i32, addr, len as u32) }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   connect() will return 0 when success and -1 when fail
     */
    pub fn connet_syscall(&self, virtual_fd: u64, addr: *const sockaddr, len: u64) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe { libc::connect(kernel_fd as i32, addr, len as u32) }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   sendto() will return the number of bytes sent, and -1 when fail
     */
    pub fn sendto_syscall(
        &self,
        virtual_fd: u64,
        buf: *const u8,
        buflen: u64,
        flags: u64,
        dest_addr: *const sockaddr,
        addrlen: u64,
    ) -> isize {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe {
            libc::sendto(
                kernel_fd as i32,
                buf as *const c_void,
                buflen as usize,
                flags as i32,
                dest_addr,
                addrlen as u32,
            )
        }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   send() will return the number of bytes sent, and -1 when fail
     */
    pub fn send_syscall(
        &self,
        virtual_fd: u64,
        buf: *const u8,
        buflen: u64,
        flags: u64,
    ) -> isize {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe { libc::send(kernel_fd as i32, buf as *const c_void, buflen as usize, flags as i32) }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   recvfrom() will return
     *       - Success: the length of the message in bytes
     *       - No messages are available to be received and the
     *           peer has performed an orderly shutdown: 0
     *       - Fail: -1
     */
    pub fn recvfrom_syscall(
        &self,
        virtual_fd: u64,
        buf: *mut u8,
        buflen: u64,
        flags: u64,
        addr: *mut sockaddr,
        addrlen: *mut u32,
    ) -> isize {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap(); 
        unsafe { libc::recvfrom(kernel_fd as i32, buf as *mut c_void, buflen as usize, flags as i32, addr, addrlen) }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   recv() will return
     *       - Success: the length of the message in bytes
     *       - No messages are available to be received and the
     *           peer has performed an orderly shutdown: 0
     *       - Fail: -1
     */
    pub fn recv_syscall(&self, virtual_fd: u64, buf: *mut c_void, len: u64, flags: u64) -> isize {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe { libc::recv(kernel_fd as i32, buf, len as usize, flags as i32) }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   listen() will return 0 when success and -1 when fail
     */
    pub fn listen_syscall(&self, virtual_fd: u64, backlog: u64) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe { libc::listen(kernel_fd as i32, backlog as i32) }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   shutdown() will return 0 when success and -1 when fail
     */
    pub fn shutdown_syscall(&self, virtual_fd: u64, how: u64) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe { libc::shutdown(kernel_fd as i32, how as i32) }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   accept() will return a file descriptor for the accepted socket
     *   Mapping a new virtual fd in this cage (virtual fd is different per cage) and kernel
     *       fd that libc::accept returned
     *   Return the virtual fd
     */
    pub fn accept_syscall(
        &self,
        virtual_fd: u64,
        addr: *mut sockaddr,
        address_len: *mut u32,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        let ret_kernelfd = unsafe { libc::accept(kernel_fd as i32, addr, address_len) };
        let ret_virtualfd = get_unused_virtual_fd(self.cageid, kernel_fd, false, 0).unwrap();
        ret_virtualfd as i32
    }

    /* 
    *   fd_set is used in the Linux select system call to specify the file descriptor 
    *   to be monitored. fd_set is actually a bit array, each bit of which represents 
    *   a file descriptor. fd_set is a specific data type used by the kernel, so we need 
    *   to make sure the final variable we pass to the kernel is in the format that the 
    *   kernel expects. That's why we choose to use FD_SET function instead of doing 
    *   bitmask by ourself. We use Vec to express the fd_set of the virtual file descriptor 
    *   in Lind, and expand the conversion function between lind fd_set and kernel fd_set.
    *
    *   We chose to use bit-set to implement our own fd_set data structure because bit-set 
    *   provides efficient set operations, allowing us to effectively represent and manipulate 
    *   file descriptor sets. These operations can maximize the fidelity to the POSIX fd_set 
    *   characteristics.
    *   Reference: https://docs.rs/bit-set/latest/bit_set/struct.BitSet.html
    *
    *   select() will return:
    *       - the total number of bits that are set in readfds, writefds, errorfds
    *       - 0, if the timeout expired before any file descriptors became ready
    *       - -1, fail
    */
    pub fn select_syscall(
        &self,
        nfds: u64,
        readfds: *mut BitSet,
        writefds: *mut BitSet,
        errorfds: *mut BitSet,
        timeout: *mut timeval,
    ) -> i32 {
        // Translate from virtual fd_set to real fd_set and then get the *mut potiner for fd_set structure
        let real_readfds = match virtual_to_real_set(self.cageid, readfds) {
            Some(real_set) => &real_set as *const _ as *mut _,
            None => ptr::null_mut(),
        };
        let real_writefds = match virtual_to_real_set(self.cageid, writefds) {
            Some(real_set) => &real_set as *const _ as *mut _,
            None => ptr::null_mut(),
        };
        let real_errorfds = match virtual_to_real_set(self.cageid, errorfds) {
            Some(real_set) => &real_set as *const _ as *mut _,
            None => ptr::null_mut(),
        };
        unsafe { libc::select(nfds as i32, real_readfds, real_writefds, real_errorfds, timeout) }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   getsockopt() will return 0 when success and -1 when fail
     */
    pub fn getsockopt_syscall(
        &self,
        virtual_fd: u64,
        level: u64,
        optname: u64,
        optval: *mut libc::c_void,
        optlen: *mut u32,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe { libc::getsockopt(kernel_fd as i32, level as i32, optname as i32, optval, optlen) }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   setsockopt() will return 0 when success and -1 when fail
     */
    pub fn setsockopt_syscall(
        &self,
        virtual_fd: u64,
        level: u64,
        optname: u64,
        optval: *mut libc::c_void,
        optlen: u64,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe { libc::setsockopt(kernel_fd as i32, level as i32, optname as i32, optval, optlen as u32) }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   getpeername() will return 0 when success and -1 when fail
     */
    pub fn getpeername_syscall(
        &self,
        virtual_fd: u64,
        address: *mut sockaddr,
        address_len: *mut u32,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe { libc::getpeername(kernel_fd as i32, address, address_len) }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   getsockname() will return 0 when success and -1 when fail
     */
    pub fn getsockname_syscall(
        &self,
        virtual_fd: u64,
        address: *mut sockaddr,
        address_len: *mut u32,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe { libc::getsockname(kernel_fd as i32, address, address_len) }
    }

    /*  
     *   gethostname() will return 0 when success and -1 when fail
     */
    pub fn gethostname_syscall(&self, name: *mut i8, len: u64) -> i32 {
        unsafe { libc::gethostname(name, len as usize) }
    }

    
    /* 
    *   In Linux, there is a specific structure pollfd used to pass file descriptors and their 
    *   related event information. Through the poll() function, multiple file descriptors can be 
    *   monitored at the same time, and different event monitoring can be set for each file 
    *   descriptor. We implement our PollStruct and related helper functions to do translation 
    *   between virtual fd and kernel fd, in order to use kernel system calls. The ownership of 
    *   poll_fd should be moved once the functions returns.
    *
    *   poll() will return:
    *   - a nonnegative value which is the number of elements in the pollfds whose revents 
    *   fields have been set to a nonzero value (indicating an event or an error)
    *   - the system call timed out before any file descriptors became ready
    *   - -1, fail
    */
    pub fn poll_syscall(
        &self,
        virtual_fds: *mut Vec<PollStruct>, // lots of fds, a ptr
        nfds: u64,
        timeout: u64,
    ) -> i32 {
        let mut real_fd = virtual_to_real_poll(self.cageid, virtual_fds);
        unsafe { libc::poll(real_fd.as_mut_ptr(), nfds as u32, timeout as i32) }
    }

    /*  
     *   Mapping a new virtual fd and kernel fd that libc::epoll_create returned
     *   Then return virtual fd
     */
    pub fn epoll_create_syscall(&self, size: i32) -> i32 {
        let kernel_fd = unsafe { libc::epoll_create(size) };
        return get_unused_virtual_fd(self.cageid, kernel_fd, false, 0).unwrap() as i32;
    }

    /*  
    *  epoll_ctl system call is used to add, modify, or remove entries in the
       interest list of the epoll(7) instance referred to by the file
       descriptor epfd.  It requests that the operation op be performed
       for the target file descriptor, fd.
    *   Translate before calling
    *   epoll_ctl() will return 0 when success and -1 when fail
    */
    pub fn epoll_ctl_syscall(
        &self,
        virtual_epfd: u64,
        op: u64,
        virtual_fd: u64,
        event: *mut epoll_event,
    ) -> i32 {
        let kernel_epfd = translate_virtual_fd(self.cageid, virtual_epfd).unwrap();
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe { libc::epoll_ctl(kernel_epfd, op as i32, kernel_fd, event) }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   epoll_wait() will return:
     *       1. the number of file descriptors ready for the requested I/O
     *       2. 0, if none
     *       3. -1, fail
     */
    pub fn epoll_wait_syscall(
        &self,
        virtual_epfd: u64,
        events: *mut epoll_event,
        maxevents: u64,
        timeout: u64,
    ) -> i32 {
        let kernel_epfd = translate_virtual_fd(self.cageid, virtual_epfd).unwrap();
        unsafe { libc::epoll_wait(kernel_epfd as i32, events, maxevents as i32, timeout as i32) }
    }

    /*   [TODO]
     *   socketpair() will return 0 when success and -1 when fail
     */
    pub fn socketpair_syscall(
        &self,
        domain: u64,
        type_: u64,
        protocol: u64,
        virtual_socket_vector: *mut Vec<u64>,
    ) -> i32 {
        // Change from pointer to reference
        let virtual_socket_vector = unsafe { &mut *virtual_socket_vector };
        if virtual_socket_vector.len() < 2 {
            panic!("virtual_socket_vector does not have enough elements");
        }
        let (vsv_1, vsv_2) = (virtual_socket_vector[0], virtual_socket_vector[1]);
        let ksv_1 = translate_virtual_fd(self.cageid, vsv_1).unwrap();
        let ksv_2 = translate_virtual_fd(self.cageid, vsv_2).unwrap();

        let mut kernel_socket_vector: [i32; 2] = [ksv_1 as i32, ksv_2 as i32];

        unsafe { libc::socketpair(domain as i32, type_ as i32, protocol as i32, kernel_socket_vector.as_mut_ptr()) }
    }
}

/* SELECT() 
*/
pub fn virtual_to_real_set(cageid: u64, virtualfds: *mut BitSet) -> Option<fd_set> {
    if virtualfds.is_null() {
        return None;
    }
    // Change from ptr to reference
    let virtualfds = unsafe { &*virtualfds };
    let mut real_set = unsafe { std::mem::zeroed::<fd_set>() };
    for virtualfd in virtualfds.iter() {
        let real_fd = translate_virtual_fd(cageid, virtualfd as u64).unwrap() as RawFd;
        unsafe { FD_SET(real_fd, &mut real_set) };
    }

    Some(real_set)    
}

/* POLL()
*/
pub struct PollStruct {
    pub virtual_fd: u64,
    pub events: i16,
    pub revents: i16,
}

pub fn virtual_to_real_poll(cageid: u64, virtual_poll: *mut Vec<PollStruct>) -> Vec<pollfd> {
    // Change from ptr to reference
    let virtual_fds = unsafe { &mut *virtual_poll };

    let mut real_fds = Vec::with_capacity(virtual_fds.len());

    for vfd in virtual_fds.iter() {
        let real_fd = translate_virtual_fd(cageid, vfd.virtual_fd).unwrap();
        real_fds.push(
            pollfd {
                fd: real_fd as i32,
                events: vfd.events,
                revents: vfd.revents,
            }
        );

    }

    real_fds
}
