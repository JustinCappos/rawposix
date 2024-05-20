#![allow(dead_code)]
// Network related system calls
// outlines and implements all of the networking system calls that are being emulated/faked in Lind

use super::net_constants::*;
use crate::safeposix::cage::{FileDescriptor::*, *};

use libc::*;

/* A,W:
*   [Related Changes]
*    - Added some helper functions in fdtables repo
*
*   [Concern / TODO] 
*    - Use functions in fdtalbes repo? --> treat fdtables as package?
*    - Type conversion? 
*       1. For now I assume the user will use linux data structure when
*          they want to use libc functions, but for fd / fd_set they need to use our implementation..?
*       2. Kernel fd type for rust libc is i32, but our fdtables set them to u64, unsure if this 
*           will cause error in the future
*    - Need to check parameter data type and libc function data type (eg: mut / not using, etc.)
*    - The socket_vector in socketpair() ...?
*    - fds in poll() should be multiple ...?
*/

impl Cage {

    /* AW:
    *   Mapping a new virtual fd and kernel fd that libc::socket returned
    *   Then return virtual fd
    */
    pub fn socket_syscall(&self, domain: i32, socktype: i32, protocol: i32) -> i32 {
        let kernel_fd = unsafe{ libc::socket(domain, socktype, protocol) };
        /*
            get_unused_virtual_fd(cageid,realfd,is_cloexec,optionalinfo) -> Result<virtualfd, EMFILE> 
        */
        return get_unused_virtual_fd(self.cageid, kernel_fd, false, 0).unwrap();
    }

    /* AW:
    *   Get the kernel fd with provided virtual fd first
    *   bind() will return 0 when success and -1 when fail
    */
    pub fn bind_syscall(&self, virtual_fd: u64, addr: *const sockaddr, len: u32) -> i32 {
        /* 
            translate_virtual_fd(cageid: u64, virtualfd: u64) -> Result<u64, threei::RetVal> 
        */
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe{ libc::bind(kernel_fd, addr, len) }
    }
    
    /* AW:
    *   Get the kernel fd with provided virtual fd first
    *   connect() will return 0 when success and -1 when fail
    */
    pub fn connet_syscall(&self, virtual_fd: u64, addr: *const sockaddr, len: u32) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe{ libc::connect(kernel_fd, addr, len) }
    }

    /* AW:
    *   Get the kernel fd with provided virtual fd first
    *   sendto() will return the number of bytes sent, and -1 when fail
    */
    pub fn sendto_syscall(
        &self,
        virtual_fd: u64,
        buf: *const u8,
        buflen: usize,
        flags: i32,
        dest_addr: *const sockaddr,
        addrlen: u32,
    ) -> isize {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe{ libc::sendto(kernel_fd, buf as *const c_void, buflen, flags, dest_addr, addrlen) }
    }

    /* AW:
    *   Get the kernel fd with provided virtual fd first
    *   send() will return the number of bytes sent, and -1 when fail
    */
    pub fn send_syscall(&self, virtual_fd: i32, buf: *const u8, buflen: usize, flags: i32) -> isize {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe{ libc::send(kernel_fd, buf as *const c_void, buflen, flags) }
    }

    /* AW:
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
        buflen: usize,
        flags: i32,
        addr: *mut sockaddr,
        addrlen: *mut u32,
    ) -> isize {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe{ libc::recvfrom(kernel_fd, buf as *mut c_void, buflen, flags, addr, addrlen) }
    }

    /* AW:
    *   Get the kernel fd with provided virtual fd first
    *   recv() will return 
    *       - Success: the length of the message in bytes
    *       - No messages are available to be received and the 
    *           peer has performed an orderly shutdown: 0
    *       - Fail: -1
    */
    pub fn recv_syscall(
        &self,
        virtual_fd: u64,
        buf: *mut c_void,
        len: usize,
        flags: i32,
    ) -> isize {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe{ libc::recv(kernel_fd, buf, len, flags) }
    }

    /* AW:
    *   Get the kernel fd with provided virtual fd first
    *   listen() will return 0 when success and -1 when fail
    */
    pub fn listen_syscall(
        &self,
        virtual_fd: u64,
        backlog: i32,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe{ libc::listen(kernel_fd, backlog) }
    }

    /* AW:
    *   Get the kernel fd with provided virtual fd first
    *   shutdown() will return 0 when success and -1 when fail
    */
    pub fn shutdown_syscall(
        &self,
        virtual_fd: u64,
        how: i32,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe{ libc::shutdown(kernel_fd, how) }
    }

    /* AW:
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
        let ret_kernelfd = unsafe{ libc::accept(kernel_fd, addr, address_len) };
        let ret_virtualfd = get_unused_virtual_fd(self.cageid, kernel_fd, false, 0).unwrap();
        ret_virtualfd
    }

    /* AW:
    *   I assume user will use Vec to represent fd_set in lind
    *   select() will return:
    *       - the total number of bits that are set in readfds, writefds, errorfds
    *       - 0, if the timeout expired before any file descriptors became ready
    *       - -1, fail
    */
    pub fn select_syscall(
        &self,
        nfds: i32,
        readfds: *mut Vec<u64>,
        writefds: *mut Vec<u64>,
        errorfds: *mut Vec<u64>,
        timeout: *mut timeval,
    ) -> i32 {
        let real_readfds = virtual_to_real_set(self.cageid, readfds);
        let real_writefds = virtual_to_real_set(self.cageid, writefds);
        let real_writefds = virtual_to_real_set(self.cageid, errorfds);
        unsafe{ libc::select(nfds, real_readfds, real_writefds, real_writefds, timeout) }
    }

    /* AW:
    *   Get the kernel fd with provided virtual fd first
    *   getsockopt() will return 0 when success and -1 when fail
    */
    pub fn getsockopt_syscall(
        &self,
        virtual_fd: u64,
        level: i32,
        optname: i32,
        optval: *mut libc::c_void,
        optlen: *mut u32,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe{ libc::getsockopt(kernel_fd, level, optname, optval, optlen) }
    }

    /* AW:
    *   Get the kernel fd with provided virtual fd first
    *   setsockopt() will return 0 when success and -1 when fail
    */
    pub fn setsockopt_syscall(
        &self,
        virtual_fd: u64,
        level: i32,
        optname: i32,
        optval: *mut libc::c_void,
        optlen: u32,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe{ libc::setsockopt(kernel_fd, level, optname, optval, optlen) }
    }

    /* AW:
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
        unsafe{ libc::getpeername(kernel_fd, address, address_len) }
    }

    /* AW:
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
        unsafe{ libc::getsockname(kernel_fd, address, address_len) }
    }

    /* AW:
    *   gethostname() will return 0 when success and -1 when fail
    */
    pub fn gethostname_syscall(
        &self,
        name: *mut i8,
        len: usize,
    ) -> i32 {
        unsafe{ libc::gethostname(name, len) }
    }

    /* AW:
    *   [TODO] check pollfds
    */
    pub fn poll_syscall(
        &self,
        virtual_fds: &mut PollStruct,
        nfds: u32,
        timeout: i32,
    ) -> i32 { 
        let real_fd = virtual_to_real_poll(self.cageid, virtual_fds);
        unsafe{ libc::poll(real_fd, nfds, timeout) }
    }

    /* AW:
    *   Mapping a new virtual fd and kernel fd that libc::epoll_create returned
    *   Then return virtual fd
    */
    pub fn epoll_create_syscall(
        &self,
        size: i32,
    ) -> i32 {
        let kernel_fd = unsafe{ libc::epoll_create(size) };
        return get_unused_virtual_fd(self.cageid, kernel_fd, false, 0).unwrap();
    }

    /* AW:
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
        op: i32,
        virtual_fd: u64,
        event: *mut epoll_event,
    ) -> i32 {
        let kernel_epfd = translate_virtual_fd(self.cageid, virtual_epfd).unwrap();
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe{ libc::epoll_ctl(kernel_epfd, op, kernel_fd, event) }
    }

    /* AW:
    *   Get the kernel fd with provided virtual fd first
    *   epoll_wait() will return: 
    *       1. the number of file descriptors ready for the requested I/O
    *       2. 0, if none
    *       3. -1, fail
    */
    pub fn epoll_wait_syscall(
        &self,
        virtual_epfd: i32,
        events: *mut epoll_event,
        maxevents: i32,
        timeout: i32,
    ) -> i32 {
        let kernel_epfd = translate_virtual_fd(self.cageid, virtual_epfd).unwrap();
        unsafe{ libc::epoll_wait(kernel_epfd, events, maxevents, timeout) }
    }

    /* AW: [TODO]
    *   socketpair() will return 0 when success and -1 when fail
    */
    pub fn socketpair_syscall(
        &self,
        domain: i32,
        type_: i32,
        protocol: i32,
        socket_vector: *mut i32,
    ) -> i32 {
        unsafe{ libc::socketpair(domain, type_, protocol, socket_vector) }
    }
}
