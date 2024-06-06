#![allow(dead_code)]
// Network related system calls
// outlines and implements all of the networking system calls that are being emulated/faked in Lind

use super::net_constants::*;
use crate::{interface::FdSet, safeposix::cage::*};
use crate::interface;

// use crate::example_grates::vanillaglobal::*;
// use crate::example_grates::dashmapvecglobal::*;
// use crate::example_grates::muthashmaxglobal::*;
use crate::example_grates::dashmaparrayglobal::*;

use std::io::Write;
use std::io;
use libc::*;
use std::ffi::CString;
use std::ffi::CStr;

use libc::*;
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
    pub fn socket_syscall(&self, domain: i32, socktype: i32, protocol: i32) -> i32 {
        let kernel_fd = unsafe { libc::socket(domain, socktype, protocol) };
        /*
            get_unused_virtual_fd(cageid,realfd,is_cloexec,optionalinfo) -> Result<virtualfd, EMFILE>
        */
        return get_unused_virtual_fd(self.cageid, kernel_fd as u64, false, 0).unwrap() as i32;
    }

    /* 
     *   Get the kernel fd with provided virtual fd first
     *   bind() will return 0 when success and -1 when fail
     */
    pub fn bind_syscall(&self, virtual_fd: i32, addr: *const sockaddr, len: u32) -> i32 {
        /*
            translate_virtual_fd(cageid: u64, virtualfd: u64) -> Result<u64, threei::RetVal>
        */
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe { libc::bind(kernel_fd as i32, addr, len) }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   connect() will return 0 when success and -1 when fail
     */
    pub fn connect_syscall(&self, virtual_fd: i32, addr: *const sockaddr, len: u32) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe { libc::connect(kernel_fd as i32, addr, len) }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   sendto() will return the number of bytes sent, and -1 when fail
     */
    pub fn sendto_syscall(
        &self,
        virtual_fd: i32,
        buf: *const u8,
        buflen: usize,
        flags: i32,
        dest_addr: *const sockaddr,
        addrlen: u32,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe {
            libc::sendto(
                kernel_fd as i32,
                buf as *const c_void,
                buflen as usize,
                flags as i32,
                dest_addr,
                addrlen as u32,
            ) as i32
        }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   send() will return the number of bytes sent, and -1 when fail
     */
    pub fn send_syscall(
        &self,
        virtual_fd: i32,
        buf: *const u8,
        buflen: usize,
        flags: i32,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe { libc::send(kernel_fd as i32, buf as *const c_void, buflen, flags) as i32}
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
        virtual_fd: i32,
        buf: *mut u8,
        buflen: usize,
        flags: i32,
        addr: *mut sockaddr,
        addrlen: u32,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap(); 
        unsafe { libc::recvfrom(kernel_fd as i32, buf as *mut c_void, buflen as usize, flags as i32, addr, addrlen as *mut u32) as i32 }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   recv() will return
     *       - Success: the length of the message in bytes
     *       - No messages are available to be received and the
     *           peer has performed an orderly shutdown: 0
     *       - Fail: -1
     */
    pub fn recv_syscall(&self, virtual_fd: i32, buf: *mut u8, len: usize, flags: i32) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe { libc::recv(kernel_fd as i32, buf as *mut c_void, len, flags) as i32 }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   listen() will return 0 when success and -1 when fail
     */
    pub fn listen_syscall(&self, virtual_fd: i32, backlog: i32) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe { libc::listen(kernel_fd as i32, backlog) }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   shutdown() will return 0 when success and -1 when fail
     */
    pub fn shutdown_syscall(&self, virtual_fd: i32, how: i32) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe { libc::shutdown(kernel_fd as i32, how) }
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
        virtual_fd: i32,
        addr: *mut sockaddr,
        address_len: u32,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        let _ret_kernelfd = unsafe { libc::accept(kernel_fd as i32, addr, address_len as *mut u32) };
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
        nfds: i32,
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
        virtual_fd: i32,
        level: i32,
        optname: i32,
        optval: *mut u8,
        optlen: u32,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe { libc::getsockopt(kernel_fd as i32, level, optname, optval as *mut c_void, optlen as *mut u32) }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   setsockopt() will return 0 when success and -1 when fail
     */
    pub fn setsockopt_syscall(
        &self,
        virtual_fd: i32,
        level: i32,
        optname: i32,
        optval: *mut u8,
        optlen: u32,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe { libc::setsockopt(kernel_fd as i32, level, optname, optval as *mut c_void, optlen) }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   getpeername() will return 0 when success and -1 when fail
     */
    pub fn getpeername_syscall(
        &self,
        virtual_fd: i32,
        address: *mut sockaddr,
        address_len: u32,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe { libc::getpeername(kernel_fd as i32, address, address_len as *mut u32) }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   getsockname() will return 0 when success and -1 when fail
     */
    pub fn getsockname_syscall(
        &self,
        virtual_fd: i32,
        address: *mut sockaddr,
        address_len: u32,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe { libc::getsockname(kernel_fd as i32, address, address_len as *mut u32) }
    }

    /*  
     *   gethostname() will return 0 when success and -1 when fail
     */
    pub fn gethostname_syscall(&self, name: *mut u8, len: isize) -> i32 {
        unsafe { libc::gethostname(name as *mut i8, len as usize) }
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
        virtual_fds: *mut [PollStruct], // lots of fds, a ptr
        nfds: u64,
        timeout: i32,
    ) -> i32 {
        let mut real_fd = virtual_to_real_poll(self.cageid, virtual_fds);
        unsafe { libc::poll(real_fd.as_mut_ptr(), nfds as u64, timeout) }
    }

    /*  
     *   Mapping a new virtual fd and kernel fd that libc::epoll_create returned
     *   Then return virtual fd
     */
    pub fn epoll_create_syscall(&self, size: i32) -> i32 {
        let kernel_fd = unsafe { libc::epoll_create(size) };
        
        if kernel_fd < 0 {
            let err = unsafe {
                libc::__errno_location()
            };
            let err_str = unsafe {
                libc::strerror(*err)
            };
            let err_msg = unsafe {
                CStr::from_ptr(err_str).to_string_lossy().into_owned()
            };
            println!("Error message: {:?}", err_msg);
            println!("[EPOLL] size: {:?}", size);
            println!("[EPOLL] kernelfd: {:?}", kernel_fd);
            io::stdout().flush().unwrap();
            panic!();
        }
        return get_unused_virtual_fd(self.cageid, kernel_fd as u64, false, 0).unwrap() as i32;
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
        virtual_epfd: i32,
        op: i32,
        virtual_fd: i32,
        epollevent: &EpollEvent,
    ) -> i32 {
        let kernel_epfd = translate_virtual_fd(self.cageid, virtual_epfd as u64).unwrap();
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        // EpollEvent conversion
        let event = epollevent.events;
        let mut epoll_event = epoll_event {
            events: event,
            u64: kernel_fd as u64,
        };

        unsafe { libc::epoll_ctl(kernel_epfd as i32, op, kernel_fd as i32, &mut epoll_event) }
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
        virtual_epfd: i32,
        events: &[EpollEvent],
        maxevents: i32,
        timeout: i32,
    ) -> i32 {
        let kernel_epfd = translate_virtual_fd(self.cageid, virtual_epfd as u64).unwrap();
        let mut kernel_events: Vec<epoll_event> = Vec::with_capacity(maxevents as usize);
        for epollevent in events.iter() {
            let virtual_fd = epollevent.fd;
            let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
            kernel_events.push(
                epoll_event {
                    events: epollevent.events,
                    u64: kernel_fd as u64,
                }
            );
        }
        unsafe { libc::epoll_wait(kernel_epfd as i32, kernel_events.as_mut_ptr(), maxevents, timeout) }
    }

    /*  
     *   socketpair() will return 0 when success and -1 when fail
     */
    pub fn socketpair_syscall(
        &self,
        domain: i32,
        type_: i32,
        protocol: i32,
        virtual_socket_vector: &mut interface::SockPair,
    ) -> i32 {
        /* TODO: change to translate from kernel - virtual after calling sockpair */

        let mut kernel_socket_vector: [i32; 2] = [0, 0];

        let ret = unsafe { libc::socketpair(domain, type_, protocol, kernel_socket_vector.as_mut_ptr()) };
        if ret == 0 {
            let ksv_1 = kernel_socket_vector[0];
            let ksv_2 = kernel_socket_vector[1];
            let vsv_1 = get_unused_virtual_fd(self.cageid, ksv_1 as u64, false, 0).unwrap();
            let vsv_2 = get_unused_virtual_fd(self.cageid, ksv_2 as u64, false, 0).unwrap();
            virtual_socket_vector.sock1 = vsv_1 as i32;
            virtual_socket_vector.sock2 = vsv_2 as i32;
            return 0;
        }
        return -1;
    }

    // pub fn getifaddrs_syscall(&self, buf: *mut u8, count: usize) -> i32 {
    //     if NET_IFADDRS_STR.len() < count {
    //         interface::fill(
    //             buf,
    //             NET_IFADDRS_STR.len(),
    //             &NET_IFADDRS_STR.as_bytes().to_vec(),
    //         );
    //         0 // return success
    //     } else {
    //         return syscall_error(Errno::EOPNOTSUPP, "getifaddrs", "invalid ifaddrs length");
    //     }
    // }

    pub fn getdents_syscall(&self, virtual_fd: i32, buf: *mut u8, nbytes: u32) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64);
        unsafe { libc::syscall(libc::SYS_getdents as c_long, kernel_fd, buf as *mut c_void, nbytes) as i32 }
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
pub fn virtual_to_real_poll(cageid: u64, virtual_poll: *mut [PollStruct]) -> Vec<pollfd> {
    // Change from ptr to reference
    let virtual_fds = unsafe { &mut *virtual_poll };

    let mut real_fds = Vec::with_capacity(virtual_fds.len());

    for vfd in virtual_fds.iter() {
        let real_fd = translate_virtual_fd(cageid, vfd.fd as u64).unwrap();
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
