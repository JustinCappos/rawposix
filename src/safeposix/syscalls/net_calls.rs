#![allow(dead_code)]
// Network related system calls
// outlines and implements all of the networking system calls that are being emulated/faked in Lind

use super::net_constants::*;
use crate::safeposix::cage::{FileDescriptor::*, *};

use libc::*;

/* A,W:
*   [TODO] 
*    - Translate rustposix fd into native fd before calling syscalls
*    - Update fdtable after socket_syscall
*/

impl Cage {

    pub fn socket_syscall(&self, domain: i32, socktype: i32, protocol: i32) -> i32 {
        unsafe{ libc::socket(domain, socktype, protocol) }
    }

    pub fn bind_syscall(&self, fd: i32, addr: *const sockaddr, len: u32) -> i32 {
        unsafe{ libc::bind(fd, addr, len) }
    }
    
    pub fn connet_syscall(&self, fd: i32, addr: *const sockaddr, len: u32) -> i32 {
        unsafe{ libc::connect(fd, addr, len) }
    }

    pub fn sendto_syscall(
        &self,
        fd: i32,
        buf: *const u8,
        buflen: usize,
        flags: i32,
        dest_addr: *const sockaddr,
        addrlen: u32,
    ) -> isize {
        unsafe{ libc::sendto(fd, buf as *const c_void, buflen, flags, dest_addr, addrlen) }
    }

    pub fn send_syscall(&self, fd: i32, buf: *const u8, buflen: usize, flags: i32) -> isize {
        unsafe{ libc::send(fd, buf as *const c_void, buflen, flags) }
    }

    pub fn recvfrom_syscall(
        &self,
        fd: i32,
        buf: *mut u8,
        buflen: usize,
        flags: i32,
        addr: *mut sockaddr,
        addrlen: *mut u32,
    ) -> isize {
        unsafe{ libc::recvfrom(fd, buf as *mut c_void, buflen, flags, addr, addrlen) }
    }

    pub fn recv_syscall(
        &self,
        fd: i32,
        buf: *mut c_void,
        len: usize,
        flags: i32,
    ) -> isize {
        unsafe{ libc::recv(fd, buf, len, flags) }
    }

    pub fn listen_syscall(
        &self,
        fd: i32,
        backlog: i32,
    ) -> i32 {
        unsafe{ libc::listen(fd, backlog) }
    }

    pub fn netshutdown_syscall(
        &self,
        fd: i32,
        how: i32,
    ) -> i32 {
        unsafe{ libc::shutdown(fd, how) }
    }

    pub fn accept_syscall(
        &self,
        fd: i32,
        addr: *mut sockaddr,
        address_len: *mut u32,
    ) -> i32 {
        unsafe{ libc::accept(fd, addr, address_len) }
    }

    pub fn select_syscall(
        &self,
        nfds: i32,
        readfds: *mut fd_set,
        writefds: *mut fd_set,
        errorfds: *mut fd_set,
        timeout: *mut timeval,
    ) -> i32 {
        unsafe{ libc::select(nfds, readfds, writefds, errorfds, timeout) }
    }

    pub fn getsockopt_syscall(
        &self,
        fd: i32,
        level: i32,
        optname: i32,
        optval: *mut libc::c_void,
        optlen: *mut u32,
    ) -> i32 {
        unsafe{ libc::getsockopt(fd, level, optname, optval, optlen) }
    }

    pub fn setsockopt_syscall(
        &self,
        fd: i32,
        level: i32,
        optname: i32,
        optval: *mut libc::c_void,
        optlen: u32,
    ) -> i32 {
        unsafe{ libc::setsockopt(fd, level, optname, optval, optlen) }
    }

    pub fn getpeername_syscall(
        &self,
        fd: i32,
        address: *mut sockaddr,
        address_len: *mut u32,
    ) -> i32 {
        unsafe{ libc::getpeername(fd, address, address_len) }
    }

    pub fn getsockname_syscall(
        &self,
        fd: i32,
        address: *mut sockaddr,
        address_len: *mut u32,
    ) -> i32 {
        unsafe{ libc::getsockname(fd, address, address_len) }
    }

    pub fn gethostname_syscall(
        &self,
        name: *mut i8,
        len: usize,
    ) -> i32 {
        unsafe{ libc::gethostname(name, len) }
    }

    pub fn poll_syscall(
        &self,
        fds: *mut pollfd,
        nfds: u32,
        timeout: i32,
    ) -> i32 { 
        unsafe{ libc::poll(fds, nfds, timeout) }
    }

    // pub fn epoll_create_syscall(
    //     &self,
    //     size: i32,
    // ) -> i32 {
    //     unsafe{ libc::epoll_create(size) }
    // }

    // pub fn epoll_ctl_syscall(
    //     &self,

    // ) -> i32 {
    //     unsafe{ libc::epoll_ctl()}
    // }

    // pub fn epoll_wait_syscall(
    //     &self,

    // ) -> i32 {
    //     unsafe{ libc::epoll_wait() }
    // }

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
