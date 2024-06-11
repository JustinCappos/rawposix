#![allow(dead_code)]
// Network related system calls
// outlines and implements all of the networking system calls that are being emulated/faked in Lind

use super::net_constants::*;
use crate::{interface::FdSet, safeposix::cage::*};
use crate::interface::*;

// use crate::example_grates::vanillaglobal::*;
use crate::example_grates::dashmapvecglobal::*;
// use crate::example_grates::muthashmaxglobal::*;
// use crate::example_grates::dashmaparrayglobal::*;

use std::collections::HashSet;
use std::collections::HashMap;
use parking_lot::Mutex;
use lazy_static::lazy_static;
use std::io::{Read, Write};
use std::io;
use std::mem::size_of;
use libc::*;
use std::ffi::CString;
use std::ffi::CStr;

use libc::*;
use std::{os::fd::RawFd, ptr};
use bit_set::BitSet;

lazy_static! {
    // A hashmap used to store epoll mapping relationships 
    // <virtual_epfd <kernel_fd, virtual_fd>> 
    static ref REAL_EPOLL_MAP: Mutex<HashMap<u64, HashMap<i32, u64>>> = Mutex::new(HashMap::new());
}

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
    pub fn bind_syscall(&self, virtual_fd: i32, addr: &GenSockaddr) -> i32 {
        /*
            translate_virtual_fd(cageid: u64, virtualfd: u64) -> Result<u64, threei::RetVal>
        */
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();

        let (finalsockaddr, addrlen) = match addr {
            GenSockaddr::V6(addrref6) => (
                (addrref6 as *const SockaddrV6).cast::<libc::sockaddr>(),
                size_of::<SockaddrV6>(),
            ),
            GenSockaddr::V4(addrref) => (
                (addrref as *const SockaddrV4).cast::<libc::sockaddr>(),
                size_of::<SockaddrV4>(),
            ),
            GenSockaddr::Unix(addrrefu) => (
                (addrrefu as *const SockaddrUnix).cast::<libc::sockaddr>(),
                size_of::<SockaddrUnix>(),
            )
        };

        let ret = unsafe { libc::bind(kernel_fd as i32, finalsockaddr, addrlen as u32) };
        if ret < 0 {
            let err = unsafe {
                libc::__errno_location()
            };
            let err_str = unsafe {
                libc::strerror(*err)
            };
            let err_msg = unsafe {
                CStr::from_ptr(err_str).to_string_lossy().into_owned()
            };
            println!("[Bind] Error message: {:?}", err_msg);
            io::stdout().flush().unwrap();
            panic!();
        }
        // println!("[Bind] GenSockAddr addr: {:?}\nGenSockAddr port: {:?}\nGenSockAddr family: {:?}", addr.addr(), addr.port(), addr.get_family());
        // println!("[Bind] GenSockaddr after: {:?}", addr);
        // io::stdout().flush().unwrap();

        ret
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   connect() will return 0 when success and -1 when fail
     */
    pub fn connect_syscall(&self, virtual_fd: i32, addr: &GenSockaddr) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();

        let (finalsockaddr, addrlen) = match addr {
            GenSockaddr::V6(addrref6) => (
                (addrref6 as *const SockaddrV6).cast::<libc::sockaddr>(),
                size_of::<SockaddrV6>(),
            ),
            GenSockaddr::V4(addrref) => (
                (addrref as *const SockaddrV4).cast::<libc::sockaddr>(),
                size_of::<SockaddrV4>(),
            ),
            GenSockaddr::Unix(addrrefu) => (
                (addrrefu as *const SockaddrUnix).cast::<libc::sockaddr>(),
                size_of::<SockaddrUnix>(),
            )
        };

        let ret = unsafe { libc::connect(kernel_fd as i32, finalsockaddr, addrlen as u32) };
        if ret < 0 {
            let err = unsafe {
                libc::__errno_location()
            };
            let err_str = unsafe {
                libc::strerror(*err)
            };
            let err_msg = unsafe {
                CStr::from_ptr(err_str).to_string_lossy().into_owned()
            };
            println!("[Connect] Error message: {:?}", err_msg);
            io::stdout().flush().unwrap();
            panic!();
        }

        // println!("[Connect] kernel fd: {:?}", kernel_fd);
        // io::stdout().flush().unwrap();
        ret
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
        dest_addr: &GenSockaddr,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();

        let (finalsockaddr, addrlen) = match dest_addr {
            GenSockaddr::V6(addrref6) => (
                (addrref6 as *const SockaddrV6).cast::<libc::sockaddr>(),
                size_of::<SockaddrV6>(),
            ),
            GenSockaddr::V4(addrref) => (
                (addrref as *const SockaddrV4).cast::<libc::sockaddr>(),
                size_of::<SockaddrV4>(),
            ),
            GenSockaddr::Unix(addrrefu) => (
                (addrrefu as *const SockaddrUnix).cast::<libc::sockaddr>(),
                size_of::<SockaddrUnix>(),
            )
        };

        unsafe {
            libc::sendto(
                kernel_fd as i32,
                buf as *const c_void,
                buflen,
                flags,
                finalsockaddr,
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
        let ret = unsafe { libc::send(kernel_fd as i32, buf as *const c_void, buflen, flags) as i32};
        if ret < 0 {
            let err = unsafe {
                libc::__errno_location()
            };
            let err_str = unsafe {
                libc::strerror(*err)
            };
            let err_msg = unsafe {
                CStr::from_ptr(err_str).to_string_lossy().into_owned()
            };
            println!("[Send] Error message: {:?}", err_msg);
            println!("[Send] kernel fd: {:?}", kernel_fd);
            io::stdout().flush().unwrap();
            panic!();
        }
        ret
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
        addr: &mut Option<&mut GenSockaddr>,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap(); 

        let (finalsockaddr, mut addrlen) = match addr {
            Some(GenSockaddr::V6(ref mut addrref6)) => (
                (addrref6 as *mut SockaddrV6).cast::<libc::sockaddr>(),
                size_of::<SockaddrV6>() as u32,
            ),
            Some(GenSockaddr::V4(ref mut addrref)) => (
                (addrref as *mut SockaddrV4).cast::<libc::sockaddr>(),
                size_of::<SockaddrV4>() as u32,
            ),
            Some(_) => {
                unreachable!()
            }
            None => (std::ptr::null::<libc::sockaddr>() as *mut libc::sockaddr, 0),
        };

        let ret = unsafe { libc::recvfrom(kernel_fd as i32, buf as *mut c_void, buflen, flags, finalsockaddr, &mut addrlen as *mut u32) as i32 };

        if ret < 0 {
            let err = unsafe {
                libc::__errno_location()
            };
            let err_str = unsafe {
                libc::strerror(*err)
            };
            let err_msg = unsafe {
                CStr::from_ptr(err_str).to_string_lossy().into_owned()
            };
            println!("[Recvfrom] Error message: {:?}", err_msg);
            println!("[Recvfrom] addr: {:?}", addr);
            io::stdout().flush().unwrap();
            panic!();
        }
        ret
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
        let ret = unsafe { libc::recv(kernel_fd as i32, buf as *mut c_void, len, flags) as i32 };
        if ret < 0 {
            let err = unsafe {
                libc::__errno_location()
            };
            let err_str = unsafe {
                libc::strerror(*err)
            };
            let err_msg = unsafe {
                CStr::from_ptr(err_str).to_string_lossy().into_owned()
            };
            println!("[Recv] Error message: {:?}", err_msg);
            println!("[Recv] kernel fd: {:?}", kernel_fd);
            io::stdout().flush().unwrap();
            panic!();
        }
        ret
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   listen() will return 0 when success and -1 when fail
     */
    pub fn listen_syscall(&self, virtual_fd: i32, backlog: i32) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        let ret = unsafe { libc::listen(kernel_fd as i32, backlog) };
        if ret < 0 {
            let err = unsafe {
                libc::__errno_location()
            };
            let err_str = unsafe {
                libc::strerror(*err)
            };
            let err_msg = unsafe {
                CStr::from_ptr(err_str).to_string_lossy().into_owned()
            };
            println!("[Listen] Error message: {:?}", err_msg);
            io::stdout().flush().unwrap();
            panic!();
        }
        ret
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
    *   We pass a default addr to libc::accept and then fill the GenSockaddr when return to 
    *   dispatcher
    *
    *   Get the kernel fd with provided virtual fd first
    *   accept() will return a file descriptor for the accepted socket
    *   Mapping a new virtual fd in this cage (virtual fd is different per cage) and kernel
    *       fd that libc::accept returned
    *   Return the virtual fd
    */
    pub fn accept_syscall(
        &self,
        virtual_fd: i32,
        _addr: &mut Option<&mut GenSockaddr>,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();

        let finalsockaddr = std::ptr::null::<libc::sockaddr>() as *mut libc::sockaddr;
        
        let mut sadlen = 0 as u32;

        let ret_kernelfd = unsafe { libc::accept(kernel_fd as i32, finalsockaddr, &mut sadlen as *mut u32) };

        if ret_kernelfd < 0 {
            let errno = unsafe {
                *libc::__errno_location() 
            } as i32;
            // println!("[Accept] errno: {:?}", errno);
            // io::stdout().flush().unwrap();
            if errno == EAGAIN {
                return syscall_error(Errno::EAGAIN, "accept", "Resource temporarily unavailable");
            }
        }
        let ret_virtualfd = get_unused_virtual_fd(self.cageid, ret_kernelfd as u64, false, 0).unwrap();
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
        mut readfds: Option<&mut fd_set>,
        mut writefds: Option<&mut fd_set>,
        mut errorfds: Option<&mut fd_set>,
        // timeout: *mut timeval,
        rposix_timeout: Option<RustDuration>,
    ) -> i32 {
        // println!("[Select] readfds: {:?}", readfds);
        // io::stdout().flush().unwrap();

        let mut timeout;
        if rposix_timeout.is_none() {
            timeout = libc::timeval { 
                tv_sec: 0, 
                tv_usec: 0,
            };
        } else {
            timeout = libc::timeval { 
                tv_sec: rposix_timeout.unwrap().as_secs() as i64, 
                tv_usec: rposix_timeout.unwrap().subsec_micros() as i64,
            };
        }
        

        let orfds = readfds.as_mut().map(|fds| &mut **fds);
        let owfds = writefds.as_mut().map(|fds| &mut **fds);
        let oefds = errorfds.as_mut().map(|fds| &mut **fds);
        let (newnfds, mut real_readfds, mut real_writefds, mut real_errorfds, _unrealset, mappingtable) 
            = get_real_bitmasks_for_select(
                self.cageid,
                nfds as u64,
                orfds.copied(),
                owfds.copied(),
                oefds.copied(),
            ).unwrap();

        // println!("[Select] Before kernel select real_readfds: {:?}", real_readfds);
        // println!("[Select] Before kernel select timeout: {:?}\nrposix_timeout: {:?}", timeout, rposix_timeout);
        // io::stdout().flush().unwrap();

        let ret = unsafe { 
            libc::select(
                newnfds as i32, 
                &mut real_readfds as *mut fd_set, 
                &mut real_writefds as *mut fd_set, 
                &mut real_errorfds as *mut fd_set, 
                &mut timeout as *mut timeval)
        };

        // println!("[Select] After kernel select real_readfds: {:?}", real_readfds);
        // io::stdout().flush().unwrap();

        if ret < 0 {
            let err = unsafe {
                libc::__errno_location()
            };
            let err_str = unsafe {
                libc::strerror(*err)
            };
            let err_msg = unsafe {
                CStr::from_ptr(err_str).to_string_lossy().into_owned()
            };
            println!("[Select] Error message: {:?}", err_msg);
            io::stdout().flush().unwrap();
        }

        // Revert result
        let (_retnfds, retreadfds, retwritefds, reterrorfds) = get_virtual_bitmasks_from_select_result(
            newnfds as u64,
            real_readfds,
            real_writefds,
            real_errorfds,
            HashSet::new(),
            HashSet::new(),
            HashSet::new(),
            &mappingtable,
        ).unwrap();
        
        // println!("[Select] retreadfds: {:?}", retreadfds);
        // println!("[Select] mappingtable: {:?}", mappingtable);
        // io::stdout().flush().unwrap();

        if let Some(rfds) = readfds.as_mut() {
            **rfds = retreadfds;
        }

        if let Some(wfds) = writefds.as_mut() {
            **wfds = retwritefds;
        }

        if let Some(efds) = errorfds.as_mut() {
            **efds = reterrorfds;
        }
        // println!("[Select] readfds: {:?}", readfds);
        // io::stdout().flush().unwrap();
        // println!("[Select] ret: {:?}", ret);
        // io::stdout().flush().unwrap();

        ret
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
        let ret = unsafe { libc::getsockopt(kernel_fd as i32, level, optname, optval as *mut c_void, optlen as *mut u32) };
        if ret < 0 {
            let err = unsafe {
                libc::__errno_location()
            };
            let err_str = unsafe {
                libc::strerror(*err)
            };
            let err_msg = unsafe {
                CStr::from_ptr(err_str).to_string_lossy().into_owned()
            };
            println!("[Getsockopt] Error message: {:?}", err_msg);
            io::stdout().flush().unwrap();
            panic!();
        }
        ret
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
        let ret = unsafe { 
            libc::setsockopt(kernel_fd as i32, level, optname, optval as *mut c_void, optlen)
        };
        if ret < 0 {
            let err = unsafe {
                libc::__errno_location()
            };
            let err_str = unsafe {
                libc::strerror(*err)
            };
            let err_msg = unsafe {
                CStr::from_ptr(err_str).to_string_lossy().into_owned()
            };
            println!("[Setsockopt] Error message: {:?}", err_msg);
            io::stdout().flush().unwrap();
            panic!();
        }
        ret
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   getpeername() will return 0 when success and -1 when fail
     */
    pub fn getpeername_syscall(
        &self,
        virtual_fd: i32,
        address: &mut Option<&mut GenSockaddr>
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        
        let (finalsockaddr, addrlen) = match address {
            Some(GenSockaddr::V6(ref mut addrref6)) => (
                (addrref6 as *mut SockaddrV6).cast::<libc::sockaddr>(),
                size_of::<SockaddrV6>() as u32,
            ),
            Some(GenSockaddr::V4(ref mut addrref)) => (
                (addrref as *mut SockaddrV4).cast::<libc::sockaddr>(),
                size_of::<SockaddrV4>() as u32,
            ),
            Some(_) => {
                unreachable!()
            }
            None => (std::ptr::null::<libc::sockaddr>() as *mut libc::sockaddr, 0),
        };

        unsafe { libc::getpeername(kernel_fd as i32, finalsockaddr, addrlen as *mut u32) }
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   getsockname() will return 0 when success and -1 when fail
     */
    pub fn getsockname_syscall(
        &self,
        virtual_fd: i32,
        address: &mut Option<&mut GenSockaddr>,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();

        let (finalsockaddr, addrlen) = match address {
            Some(GenSockaddr::V6(ref mut addrref6)) => (
                (addrref6 as *mut SockaddrV6).cast::<libc::sockaddr>(),
                size_of::<SockaddrV6>() as u32,
            ),
            Some(GenSockaddr::V4(ref mut addrref)) => (
                (addrref as *mut SockaddrV4).cast::<libc::sockaddr>(),
                size_of::<SockaddrV4>() as u32,
            ),
            Some(_) => {
                unreachable!()
            }
            None => (std::ptr::null::<libc::sockaddr>() as *mut libc::sockaddr, 0),
        };

        unsafe { libc::getsockname(kernel_fd as i32, finalsockaddr, addrlen as *mut u32) }
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
        virtual_fds: &mut [PollStruct], // lots of fds, a ptr
        nfds: u64,
        timeout: i32,
    ) -> i32 {
        let mut real_fd = virtual_to_real_poll(self.cageid, virtual_fds);
        let ret = unsafe { libc::poll(real_fd.as_mut_ptr(), nfds as u64, timeout) };
        if ret < 0 {
            let err = unsafe {
                libc::__errno_location()
            };
            let err_str = unsafe {
                libc::strerror(*err)
            };
            let err_msg = unsafe {
                CStr::from_ptr(err_str).to_string_lossy().into_owned()
            };
            println!("[POLL] Error message: {:?}", err_msg);
            println!("[POLL] kernel fd: {:?}", real_fd);
            io::stdout().flush().unwrap();
            panic!();
        }

        // Convert back to PollStruct
        for (i, libcpoll) in real_fd.iter().enumerate() {
            if let Some(rposix_poll) = virtual_fds.get_mut(i) {
                rposix_poll.revents = libcpoll.revents;
            }
        }
        
        ret
    }

    /* EPOLL
    *   In normal Linux, epoll will perform the listed behaviors 
    *   
    *   epoll_create:
    *   - This function creates an epfd, which is an epoll file descriptor used to manage 
    *       multiple file behaviors.
    *   epoll_ctl:
    *   - This function associates the events and the file descriptors that need to be 
    *       monitored with the specific epfd.
    *   epoll_wait:
    *   - This function waits for events on the epfd and returns a list of epoll_events 
    *       that have been triggered.
    *   
    *   Then the processing workflow in RawPOSIX is:
    *
    *   epoll_create:
    *   When epoll_create is called, we use epoll_create_helper to create a virtual epfd.
    *   Add this virtual epfd to the global mapping table.
    *
    *   epoll_ctl:
    *   (Use try_epoll_ctl to handle the association between the virtual epfd and the 
    *   events with the file descriptors.) This step involves updating the global table 
    *   with the appropriate mappings.
    *
    *   epoll_wait:
    *   When epoll_wait is called, you need to convert the virtual epfd to the real epfd.
    *   Call libc::epoll_wait to perform the actual wait operation on the real epfd.
    *   Convert the resulting real events back to the virtual events using the mapping in 
    *   the global table.
    */

    /*  
     *   Mapping a new virtual fd and kernel fd that libc::epoll_create returned
     *   Then return virtual fd
     */
    pub fn epoll_create_syscall(&self, size: i32) -> i32 {
        // Create the kernel instance
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
            return -1;
        }

        // Get the virtual epfd
        let virtual_epfd = get_unused_virtual_fd(self.cageid, kernel_fd as u64, false, 0).unwrap();
        // println!("[epoll_create] virtual_epfd: {:?}", virtual_epfd);
        // io::stdout().flush().unwrap();

        // We don't need to update mapping table at now
        // Return virtual epfd
        virtual_epfd as i32
        
    }

    /*  
    *   Translate before calling, and updating the glocal mapping tables according to 
    *   the op. 
    *   epoll_ctl() will return 0 when success and -1 when fail
    */
    pub fn epoll_ctl_syscall(
        &self,
        virtual_epfd: i32,
        op: i32,
        virtual_fd: i32,
        epollevent: &mut EpollEvent,
    ) -> i32 {

        let kernel_epfd = translate_virtual_fd(self.cageid, virtual_epfd as u64).unwrap();
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        // EpollEvent conversion
        let event = epollevent.events;
        let mut epoll_event = epoll_event {
            events: event,
            u64: kernel_fd as u64,
        };

        let ret = unsafe { libc::epoll_ctl(kernel_epfd as i32, op, kernel_fd as i32, &mut epoll_event) };
        if ret < 0 {
            let err = unsafe {
                libc::__errno_location()
            };
            let err_str = unsafe {
                libc::strerror(*err)
            };
            let err_msg = unsafe {
                CStr::from_ptr(err_str).to_string_lossy().into_owned()
            };
            println!("[epoll_ctl] Error message: {:?}", err_msg);
            io::stdout().flush().unwrap();
            return -1;
        }

        // Update the virtual list -- but we only handle the non-real fd case
        //  try_epoll_ctl will directly return a real fd in libc case
        //  - maybe we could create a new mapping table to handle the mapping relationship..?
        //      ceate inside the fdtable interface? or we could handle inside rawposix..?
        
        // Update the mapping table for epoll
        if op == libc::EPOLL_CTL_DEL {
            let mut epollmapping = REAL_EPOLL_MAP.lock();
            if let Some(fdmap) = epollmapping.get_mut(&(virtual_epfd as u64)) {
                if fdmap.remove(&(kernel_fd as i32)).is_some() {
                    if fdmap.is_empty() {
                        epollmapping.remove(&(virtual_epfd as u64));
                    }
                    return ret;
                }
            }
        } else {
            let mut epollmapping = REAL_EPOLL_MAP.lock();
            epollmapping.entry(virtual_epfd as u64).or_insert_with(HashMap::new).insert(kernel_fd as i32, virtual_fd as u64);
            return ret;
        }

        -1
    }

    /*  
     *   Get the kernel fd with provided virtual fd first, and then convert back to virtual
     *   epoll_wait() will return:
     *       1. the number of file descriptors ready for the requested I/O
     *       2. 0, if none
     *       3. -1, fail
     */
    pub fn epoll_wait_syscall(
        &self,
        virtual_epfd: i32,
        events: &mut [EpollEvent],
        maxevents: i32,
        timeout: i32,
    ) -> i32 {
        let kernel_epfd = translate_virtual_fd(self.cageid, virtual_epfd as u64).unwrap();
        let mut kernel_events: Vec<epoll_event> = Vec::with_capacity(maxevents as usize);

        // Should always be null value before we call libc::epoll_wait
        kernel_events.push(
            epoll_event {
                events: 0,
                u64: 0,
            }
        );

        let ret = unsafe { libc::epoll_wait(kernel_epfd as i32, kernel_events.as_mut_ptr(), maxevents, timeout as i32) };
        if ret < 0 {
            let err = unsafe {
                libc::__errno_location()
            };
            let err_str = unsafe {
                libc::strerror(*err)
            };
            let err_msg = unsafe {
                CStr::from_ptr(err_str).to_string_lossy().into_owned()
            };
            println!("[epoll_wait] Error message: {:?}", err_msg);
            io::stdout().flush().unwrap();
        }

        // Convert back to rustposix's data structure
        // Loop over virtual_epollfd to find corresponding mapping relationship between kernel fd and virtual fd
        for i in 0..ret as usize {

            let ret_kernelfd = kernel_events[i].u64;
            let epollmapping = REAL_EPOLL_MAP.lock();
            let ret_virtualfd = epollmapping.get(&(virtual_epfd as u64)).and_then(|kernel_map| kernel_map.get(&(ret_kernelfd as i32)).copied());

            events[i].fd = ret_virtualfd.unwrap() as i32;
            events[i].events = kernel_events[i].events;
        }

        ret
    }

    /*  
     *   socketpair() will return 0 when success and -1 when fail
     */
    pub fn socketpair_syscall(
        &self,
        domain: i32,
        type_: i32,
        protocol: i32,
        virtual_socket_vector: &mut SockPair,
    ) -> i32 {

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

    /*
    *   Get result back from libc::getifaddrs and fill the content of name field into a buf 
    *   as rustposix, so that i don’t need to change the dispatcher interface
    */
    pub fn getifaddrs_syscall(&self, buf: *mut u8, count: usize) -> i32 {
        let mut ifaddr: *mut ifaddrs = ptr::null_mut();

        unsafe {
            if getifaddrs(&mut ifaddr) < 0 {
                let err = libc::__errno_location();
                let err_str = libc::strerror(*err);
                let err_msg = CStr::from_ptr(err_str).to_string_lossy().into_owned();
                println!("Error message: {:?}", err_msg);
                io::stdout().flush().unwrap();
                return -1;
            }
            let mut ifa = ifaddr;
            let mut offset = 0;
            while !ifa.is_null() {
                let ifa_ref = &*ifa;
                let name_cstr = CStr::from_ptr(ifa_ref.ifa_name);
                let name_bytes = name_cstr.to_bytes();

                // Check if there's enough space in the buffer
                if offset + name_bytes.len() + 1 > count {
                    println!("Buffer size exceeded");
                    freeifaddrs(ifaddr);
                    return -1;
                }

                let name_vec = name_bytes.to_vec();
                fill(buf.add(offset), name_vec.len(), &name_vec);

                // Add a null terminator to separate names
                *buf.add(offset + name_vec.len()) = 0;
                offset += name_vec.len() + 1; // Move offset past the name and null terminator
            
                ifa = ifa_ref.ifa_next;
            
            }
            freeifaddrs(ifaddr);
            0
        }
    }

    pub fn getdents_syscall(&self, virtual_fd: i32, buf: *mut u8, nbytes: u32) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64);
        unsafe { libc::syscall(libc::SYS_getdents as c_long, kernel_fd, buf as *mut c_void, nbytes) as i32 }
    }
}

/* POLL()
*/
pub fn virtual_to_real_poll(cageid: u64, virtual_poll: &mut [PollStruct]) -> Vec<pollfd> {
    // Change from ptr to reference
    // let virtual_fds = unsafe { &mut *virtual_poll };

    let mut real_fds = Vec::with_capacity(virtual_poll.len());

    for vfd in &mut *virtual_poll {

        let real_fd = translate_virtual_fd(cageid, vfd.fd as u64).unwrap();
        let kernel_poll = pollfd {
            fd: real_fd as i32,
            events: vfd.events,
            revents: vfd.revents,
        };
        real_fds.push(kernel_poll);
    }

    real_fds
}
