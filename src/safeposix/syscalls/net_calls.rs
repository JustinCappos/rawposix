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
use std::io::Write;
use std::io;
use std::mem::size_of;
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
     *   Get the kernel fd with provided virtual fd first
     *   accept() will return a file descriptor for the accepted socket
     *   Mapping a new virtual fd in this cage (virtual fd is different per cage) and kernel
     *       fd that libc::accept returned
     *   Return the virtual fd
     */
    pub fn accept_syscall(
        &self,
        virtual_fd: i32,
        addr: &mut Option<&mut GenSockaddr>,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        
        let (finalsockaddr, addrlen) = match addr {
            Some(GenSockaddr::V6(ref mut addrref6)) => (
                (addrref6 as *mut SockaddrV6).cast::<libc::sockaddr>(),
                size_of::<SockaddrV6>() as *mut u32,
            ),
            Some(GenSockaddr::V4(ref mut addrref)) => (
                (addrref as *mut SockaddrV4).cast::<libc::sockaddr>(),
                size_of::<SockaddrV4>() as *mut u32,
            ),
            Some(GenSockaddr::Unix(ref mut addrrefu)) => (
                (addrrefu as *mut SockaddrUnix).cast::<libc::sockaddr>(),
                size_of::<SockaddrUnix>() as *mut u32,
            ),
            Some(_) => {
                unreachable!()
            }
            None => (std::ptr::null::<libc::sockaddr>() as *mut libc::sockaddr, 0 as *mut u32),
        };
        // let mut inneraddrbuf = SockaddrV4::default();

        // let mut inneraddrbuf = GenSockaddr::Unix(SockaddrUnix::default());
        let mut sadlen = size_of::<SockaddrV4>() as u32;
        // let ret_kernelfd = unsafe {
        //     libc::accept(
        //         kernel_fd as i32,
        //         (&mut inneraddrbuf as *mut SockaddrV4).cast::<libc::sockaddr>(),
        //         &mut sadlen as *mut u32,
        //     )
        // };

        let ret_kernelfd = unsafe { libc::accept(kernel_fd as i32, finalsockaddr, &mut sadlen as *mut u32) };

        if ret_kernelfd < 0 {
            let err = unsafe {
                libc::__errno_location()
            };
            let err_str = unsafe {
                libc::strerror(*err)
            };
            let err_msg = unsafe {
                CStr::from_ptr(err_str).to_string_lossy().into_owned()
            };
            println!("[Accept] Error message: {:?}", err_msg);
            println!("[Accept] GenSockaddr: {:?}", addr);
            io::stdout().flush().unwrap();
            panic!();
        }
        // println!("[Accept] GenSockaddr: {:?}", addr);
        // println!("[Accept] ret kernel fd: {:?}", ret_kernelfd);
        // io::stdout().flush().unwrap();
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
        timeout: *mut timeval,
    ) -> i32 {
        let orfds = readfds.cloned();
        let owfds = writefds.cloned();
        let oefds = errorfds.cloned();
        let (newnfds, mut real_readfds, mut real_writefds, mut real_errorfds, unrealset, mappingtable) 
            = get_real_bitmasks_for_select(
                self.cageid,
                nfds as u64,
                orfds,
                owfds,
                oefds,
            ).unwrap();

        let ret = unsafe { 
            libc::select(
                newnfds as i32, 
                &mut real_readfds as *mut fd_set, 
                &mut real_writefds as *mut fd_set, 
                &mut real_errorfds as *mut fd_set, 
                timeout)
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
        println!("[Select] Error message: {:?}", err_msg);
        io::stdout().flush().unwrap();
    }

    let unreal_notused: HashSet<u64> = HashSet::new();

    // Revert result
    let (newnfds, mut retreadfds, mut retwritefds, mut reterrorfds) = get_virtual_bitmasks_from_select_result(
        ret as u64,
        real_readfds,
        real_writefds,
        real_errorfds,
        unreal_notused.clone(),
        unreal_notused.clone(),
        unreal_notused.clone(),
        &mappingtable,
    ).unwrap();
    
    if let Some(rfds) = readfds.as_mut() {
        *rfds = &mut retreadfds;
    }

    if let Some(wfds) = writefds.as_mut() {
        *wfds = &mut retwritefds;
    }

    if let Some(efds) = errorfds.as_mut() {
        *efds = &mut reterrorfds;
    }

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
        virtual_socket_vector: &mut SockPair,
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
