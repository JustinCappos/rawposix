#![allow(dead_code)]
// Network related system calls
// outlines and implements all of the networking system calls that are being emulated/faked in Lind

use super::net_constants::*;
use crate::{interface::FdSet, safeposix::cage::*};
use crate::interface::*;

use crate::fdtables;

use std::collections::HashSet;
use std::collections::HashMap;
use std::convert::TryInto;
use parking_lot::Mutex;
use lazy_static::lazy_static;
use std::io::{Read, Write};
use std::io;
use std::mem::size_of;
use libc::*;
use std::ffi::CString;
use std::ffi::CStr;

use crate::safeposix::impipe::*;

use libc::*;
use std::{os::fd::RawFd, ptr};
use bit_set::BitSet;

static LIND_ROOT: &str = "/home/lind/lind_project/src/safeposix-rust/tmp/";
const FDKIND_KERNEL: u32 = 0;
const FDKIND_IMPIPE: u32 = 1;
const FDKIND_IMSOCK: u32 = 2;

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
        if kernel_fd < 0 {
            let errno = get_errno();
            let err_str = unsafe {
                libc::strerror(errno)
            };
            let err_msg = unsafe {
                CStr::from_ptr(err_str).to_string_lossy().into_owned()
            };
            println!("[socket] Error message: {:?}", err_msg);
            io::stdout().flush().unwrap();
            return handle_errno(errno, "socket");
        }

        return fdtables::get_unused_virtual_fd(self.cageid, FDKIND_KERNEL, kernel_fd as u64, false, 0).unwrap() as i32;
    }

    /* 
     *   Get the kernel fd with provided virtual fd first
     *   bind() will return 0 when success and -1 when fail
     */
    pub fn bind_syscall(&self, virtual_fd: i32, addr: &GenSockaddr) -> i32 {
        /*
            translate_virtual_fd(cageid: u64, virtualfd: u64) -> Result<u64, threei::RetVal>
        */
        let wrappedvfd = fdtables::translate_virtual_fd(self.cageid, virtual_fd as u64);
        if wrappedvfd.is_err() {
            return syscall_error(Errno::EBADF, "bind", "Bad File Descriptor");
        }
        let vfd = wrappedvfd.unwrap();

        // println!("[Bind] Before GenSockaddr: {:?}", addr);
        // io::stdout().flush().unwrap();
        let mut new_addr = SockaddrUnix::default();

        let (finalsockaddr, addrlen) = match addr {
            GenSockaddr::V6(addrref6) => (
                (addrref6 as *const SockaddrV6).cast::<libc::sockaddr>(),
                size_of::<SockaddrV6>(),
            ),
            GenSockaddr::V4(addrref) => (
                (addrref as *const SockaddrV4).cast::<libc::sockaddr>(),
                size_of::<SockaddrV4>(),
            ),
            GenSockaddr::Unix(addrrefu) => {
                // let original_path_ptr;
                // let original_path_len;
                // unsafe {
                //     // Skip the first '/'
                //     original_path_ptr = addrrefu.sun_path.as_ptr().add(1); 

                //     original_path_len = libc::strlen(original_path_ptr as *const i8);
                // }
                

                // // Create new path
                // let lind_root_len = LIND_ROOT.len();
                // let new_path_len = lind_root_len + original_path_len;

                // if new_path_len >= addrrefu.sun_path.len() {
                //     panic!("New path is too long to fit in sun_path");
                // }

                // let mut new_addr = SockaddrUnix {
                //     sun_family: addrrefu.sun_family,
                //     sun_path: [0; 108],
                // };

                // // First copy LIND_ROOT and then copy original path
                // unsafe {
                //     std::ptr::copy_nonoverlapping(
                //         LIND_ROOT.as_ptr(),
                //         new_addr.sun_path.as_mut_ptr(),
                //         lind_root_len
                //     );

                    
                //     std::ptr::copy_nonoverlapping(
                //         original_path_ptr,
                //         new_addr.sun_path.as_mut_ptr().add(lind_root_len),
                //         original_path_len
                //     );

                //     // End with NULL
                //     // *new_addr.sun_path.get_unchecked_mut(new_path_len) = 0;
                // }

                // (
                //     (&new_addr as *const SockaddrUnix).cast::<libc::sockaddr>(),
                //     size_of::<SockaddrUnix>(),
                // )
                // Convert sun_path to LIND_ROOT path
                let original_path = unsafe { CStr::from_ptr(addrrefu.sun_path.as_ptr() as *const i8).to_str().unwrap() };
                let lind_path = format!("{}{}", LIND_ROOT, &original_path[..]); // Skip the initial '/' in original path

                // Ensure the length of lind_path does not exceed sun_path capacity
                if lind_path.len() >= addrrefu.sun_path.len() {
                    panic!("New path is too long to fit in sun_path");
                }

                new_addr = SockaddrUnix {
                    sun_family: addrrefu.sun_family,
                    sun_path: [0; 108],
                };

                // Copy the new path into sun_path
                unsafe {
                    ptr::copy_nonoverlapping(
                        lind_path.as_ptr(),
                        new_addr.sun_path.as_mut_ptr() as *mut u8,
                        lind_path.len()
                    );
                    *new_addr.sun_path.get_unchecked_mut(lind_path.len()) = 0; // Null-terminate the string
                }

                // println!("[bind] new_addr:{:?} ", new_addr);
                // io::stdout().flush().unwrap();
                
                (
                    (&new_addr as *const SockaddrUnix).cast::<libc::sockaddr>(),
                    size_of::<SockaddrUnix>(),
                )
                
            }
            
        };

        let ret = unsafe { libc::bind(vfd.underfd as i32, finalsockaddr, addrlen as u32) };
        if ret < 0 {
            let errno = get_errno();
            let err_str = unsafe {
                libc::strerror(errno)
            };
            let err_msg = unsafe {
                CStr::from_ptr(err_str).to_string_lossy().into_owned()
            };
            unsafe {
                let sockaddr_un_ptr = finalsockaddr as *const sockaddr_un;
        
                let sun_path_ptr = (*sockaddr_un_ptr).sun_path.as_ptr();
        
                let c_str = CStr::from_ptr(sun_path_ptr);
                let str_slice = c_str.to_str().expect("Failed to convert CStr to str");
                
                println!("[bind] addr: {:?}", addr);
                println!("[bind] sun_path: {}", str_slice);
                io::stdout().flush().unwrap();
            }
            println!("[Bind] Error message: {:?}", err_msg);
            io::stdout().flush().unwrap();
            return handle_errno(errno, "bind");
        }
        ret
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   connect() will return 0 when success and -1 when fail
     */
    pub fn connect_syscall(&self, virtual_fd: i32, addr: &GenSockaddr) -> i32 {
        let wrappedvfd = fdtables::translate_virtual_fd(self.cageid, virtual_fd as u64);
        if wrappedvfd.is_err() {
            return syscall_error(Errno::EBADF, "connect", "Bad File Descriptor");
        }
        let vfd = wrappedvfd.unwrap();

        let mut new_addr = SockaddrUnix::default();

        let (finalsockaddr, addrlen) = match addr {
            GenSockaddr::V6(addrref6) => (
                (addrref6 as *const SockaddrV6).cast::<libc::sockaddr>(),
                size_of::<SockaddrV6>(),
            ),
            GenSockaddr::V4(addrref) => (
                (addrref as *const SockaddrV4).cast::<libc::sockaddr>(),
                size_of::<SockaddrV4>(),
            ),
            GenSockaddr::Unix(addrrefu) => {
                // let original_path_ptr;
                // let original_path_len;
                // unsafe {
                //     // Skip the first '/'
                //     original_path_ptr = addrrefu.sun_path.as_ptr().add(1); 

                //     original_path_len = libc::strlen(original_path_ptr as *const i8);
                // }
                

                // // Create new path
                // let lind_root_len = LIND_ROOT.len();
                // let new_path_len = lind_root_len + original_path_len;

                // if new_path_len >= addrrefu.sun_path.len() {
                //     panic!("New path is too long to fit in sun_path");
                // }

                // let mut new_addr = SockaddrUnix {
                //     sun_family: addrrefu.sun_family,
                //     sun_path: [0; 108],
                // };

                // // First copy LIND_ROOT and then copy original path
                // unsafe {
                //     std::ptr::copy_nonoverlapping(
                //         LIND_ROOT.as_ptr(),
                //         new_addr.sun_path.as_mut_ptr(),
                //         lind_root_len
                //     );

                    
                //     std::ptr::copy_nonoverlapping(
                //         original_path_ptr,
                //         new_addr.sun_path.as_mut_ptr().add(lind_root_len),
                //         original_path_len
                //     );

                //     // End with NULL
                //     *new_addr.sun_path.get_unchecked_mut(new_path_len) = 0;
                // }

                // (
                //     (&new_addr as *const SockaddrUnix).cast::<libc::sockaddr>(),
                //     size_of::<SockaddrUnix>(),
                // )
                // Convert sun_path to LIND_ROOT path
                let original_path = unsafe { CStr::from_ptr(addrrefu.sun_path.as_ptr() as *const i8).to_str().unwrap() };
                let lind_path = format!("{}{}", LIND_ROOT, &original_path[..]); // Skip the initial '/' in original path

                // Ensure the length of lind_path does not exceed sun_path capacity
                if lind_path.len() >= addrrefu.sun_path.len() {
                    panic!("New path is too long to fit in sun_path");
                }

                new_addr = SockaddrUnix {
                    sun_family: addrrefu.sun_family,
                    sun_path: [0; 108],
                };

                // Copy the new path into sun_path
                unsafe {
                    ptr::copy_nonoverlapping(
                        lind_path.as_ptr(),
                        new_addr.sun_path.as_mut_ptr() as *mut u8,
                        lind_path.len()
                    );
                    *new_addr.sun_path.get_unchecked_mut(lind_path.len()) = 0; // Null-terminate the string
                }
                // println!("[connect] new_addr:{:?} ", new_addr);
                // io::stdout().flush().unwrap();
                (
                    (&new_addr as *const SockaddrUnix).cast::<libc::sockaddr>(),
                    size_of::<SockaddrUnix>(),
                )
                
            }
        };

        let ret = unsafe { libc::connect(vfd.underfd as i32, finalsockaddr, addrlen as u32) };
        if ret < 0 {
            // let err = unsafe {
            //     libc::__errno_location()
            // };
            // let err_str = unsafe {
            //     libc::strerror(*err)
            // };
            // let err_msg = unsafe {
            //     CStr::from_ptr(err_str).to_string_lossy().into_owned()
            // };
            // println!("[Connect] Error message: {:?}", err_msg);
            // io::stdout().flush().unwrap();
            let errno = get_errno();
            return handle_errno(errno, "connect");
        }
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
        let wrappedvfd = fdtables::translate_virtual_fd(self.cageid, virtual_fd as u64);
        if wrappedvfd.is_err() {
            return syscall_error(Errno::EBADF, "sendto", "Bad File Descriptor");
        }
        let vfd = wrappedvfd.unwrap();

        let (finalsockaddr, addrlen) = match dest_addr {
            GenSockaddr::V6(addrref6) => (
                (addrref6 as *const SockaddrV6).cast::<libc::sockaddr>(),
                size_of::<SockaddrV6>(),
            ),
            GenSockaddr::V4(addrref) => (
                (addrref as *const SockaddrV4).cast::<libc::sockaddr>(),
                size_of::<SockaddrV4>(),
            ),
            GenSockaddr::Unix(addrrefu) => {
                // Convert sun_path to LIND_ROOT path
                let original_path = unsafe { CStr::from_ptr(addrrefu.sun_path.as_ptr() as *const i8).to_str().unwrap() };
                let lind_path = format!("{}{}", LIND_ROOT, &original_path[..]); // Skip the initial '/' in original path

                // Ensure the length of lind_path does not exceed sun_path capacity
                if lind_path.len() >= addrrefu.sun_path.len() {
                    panic!("New path is too long to fit in sun_path");
                }

                let mut new_addr = SockaddrUnix {
                    sun_family: addrrefu.sun_family,
                    sun_path: [0; 108],
                };

                // Copy the new path into sun_path
                unsafe {
                    ptr::copy_nonoverlapping(
                        lind_path.as_ptr(),
                        new_addr.sun_path.as_mut_ptr() as *mut u8,
                        lind_path.len()
                    );
                    *new_addr.sun_path.get_unchecked_mut(lind_path.len()) = 0; // Null-terminate the string
                }

                (
                    (&new_addr as *const SockaddrUnix).cast::<libc::sockaddr>(),
                    size_of::<SockaddrUnix>(),
                )
                
            }
        };

       let ret = unsafe {
            libc::sendto(
                vfd.underfd as i32,
                buf as *const c_void,
                buflen,
                flags,
                finalsockaddr,
                addrlen as u32,
            ) as i32
        };

        if ret < 0 {
            let errno = get_errno();
            return handle_errno(errno, "sendto");
        }

        ret
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
        let wrappedvfd = fdtables::translate_virtual_fd(self.cageid, virtual_fd as u64);
        if wrappedvfd.is_err() {
            return syscall_error(Errno::EBADF, "send", "Bad File Descriptor");
        }
        let vfd = wrappedvfd.unwrap();

        let ret = unsafe { libc::send(vfd.underfd as i32, buf as *const c_void, buflen, flags) as i32};
        if ret < 0 {
            // let err = unsafe {
            //     libc::__errno_location()
            // };
            // let err_str = unsafe {
            //     libc::strerror(*err)
            // };
            // let err_msg = unsafe {
            //     CStr::from_ptr(err_str).to_string_lossy().into_owned()
            // };
            // println!("[Send] Error message: {:?}", err_msg);
            // println!("[Send] kernel fd: {:?}", kernel_fd);
            // io::stdout().flush().unwrap();
            let errno = get_errno();
            return handle_errno(errno, "send");
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
        let wrappedvfd = fdtables::translate_virtual_fd(self.cageid, virtual_fd as u64);
        if wrappedvfd.is_err() {
            return syscall_error(Errno::EBADF, "recvfrom", "Bad File Descriptor");
        }
        let vfd = wrappedvfd.unwrap();

        let (finalsockaddr, mut addrlen) = match addr {
            Some(GenSockaddr::V6(ref mut addrref6)) => (
                (addrref6 as *mut SockaddrV6).cast::<libc::sockaddr>(),
                size_of::<SockaddrV6>() as u32,
            ),
            Some(GenSockaddr::V4(ref mut addrref)) => (
                (addrref as *mut SockaddrV4).cast::<libc::sockaddr>(),
                size_of::<SockaddrV4>() as u32,
            ),
            Some(GenSockaddr::Unix(ref mut addrrefu)) => (
                (addrrefu as *mut SockaddrUnix).cast::<libc::sockaddr>(),
                size_of::<SockaddrUnix>() as u32,
            ),
            None => (std::ptr::null::<libc::sockaddr>() as *mut libc::sockaddr, 0),
        };

        let ret = unsafe { libc::recvfrom(vfd.underfd as i32, buf as *mut c_void, buflen, flags, finalsockaddr, &mut addrlen as *mut u32) as i32 };

        if ret < 0 {
            // let err = unsafe {
            //     libc::__errno_location()
            // };
            // let err_str = unsafe {
            //     libc::strerror(*err)
            // };
            // let err_msg = unsafe {
            //     CStr::from_ptr(err_str).to_string_lossy().into_owned()
            // };
            // println!("[Recvfrom] Error message: {:?}", err_msg);
            // println!("[Recvfrom] addr: {:?}", addr);
            // io::stdout().flush().unwrap();
            let errno = get_errno();
            return handle_errno(errno, "recvfrom");
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
        let wrappedvfd = fdtables::translate_virtual_fd(self.cageid, virtual_fd as u64);
        if wrappedvfd.is_err() {
            return syscall_error(Errno::EBADF, "recv", "Bad File Descriptor");
        }
        let vfd = wrappedvfd.unwrap();

        let ret = unsafe { libc::recv(vfd.underfd as i32, buf as *mut c_void, len, flags) as i32 };
        if ret < 0 {
            // let err = unsafe {
            //     libc::__errno_location()
            // };
            // let err_str = unsafe {
            //     libc::strerror(*err)
            // };
            // let err_msg = unsafe {
            //     CStr::from_ptr(err_str).to_string_lossy().into_owned()
            // };
            // println!("[Recv] Error message: {:?}", err_msg);
            // println!("[Recv] kernel fd: {:?}", kernel_fd);
            // io::stdout().flush().unwrap();
            let errno = get_errno();
            return handle_errno(errno, "recv");
        }
        ret
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   listen() will return 0 when success and -1 when fail
     */
    pub fn listen_syscall(&self, virtual_fd: i32, backlog: i32) -> i32 {
        let wrappedvfd = fdtables::translate_virtual_fd(self.cageid, virtual_fd as u64);
        if wrappedvfd.is_err() {
            return syscall_error(Errno::EBADF, "listen", "Bad File Descriptor");
        }
        let vfd = wrappedvfd.unwrap();

        let ret = unsafe { libc::listen(vfd.underfd as i32, backlog) };
        if ret < 0 {
            // let err = unsafe {
            //     libc::__errno_location()
            // };
            // let err_str = unsafe {
            //     libc::strerror(*err)
            // };
            // let err_msg = unsafe {
            //     CStr::from_ptr(err_str).to_string_lossy().into_owned()
            // };
            // println!("[Listen] Error message: {:?}", err_msg);
            // io::stdout().flush().unwrap();
            let errno = get_errno();
            return handle_errno(errno, "listen");
        }
        ret
    }

    /*  
     *   Get the kernel fd with provided virtual fd first
     *   shutdown() will return 0 when success and -1 when fail
     */
    pub fn shutdown_syscall(&self, virtual_fd: i32, how: i32) -> i32 {
        let wrappedvfd = fdtables::translate_virtual_fd(self.cageid, virtual_fd as u64);
        if wrappedvfd.is_err() {
            return syscall_error(Errno::EBADF, "shutdown", "Bad File Descriptor");
        }
        let vfd = wrappedvfd.unwrap();

        let ret = unsafe { libc::shutdown(vfd.underfd as i32, how) };

        if ret < 0 {
            let errno = get_errno();
            return handle_errno(errno, "bind");
        }

        ret
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
        addr: &mut Option<&mut GenSockaddr>,
    ) -> i32 {
        let wrappedvfd = fdtables::translate_virtual_fd(self.cageid, virtual_fd as u64);
        if wrappedvfd.is_err() {
            return syscall_error(Errno::EBADF, "accept", "Bad File Descriptor");
        }
        let vfd = wrappedvfd.unwrap();

        let (finalsockaddr, mut addrlen) = match addr {
            Some(GenSockaddr::V6(ref mut addrref6)) => (
                (addrref6 as *mut SockaddrV6).cast::<libc::sockaddr>(),
                size_of::<SockaddrV6>() as u32,
            ),
            Some(GenSockaddr::V4(ref mut addrref)) => (
                (addrref as *mut SockaddrV4).cast::<libc::sockaddr>(),
                size_of::<SockaddrV4>() as u32,
            ),
            Some(GenSockaddr::Unix(ref mut addrrefu)) => (
                (addrrefu as *mut SockaddrUnix).cast::<libc::sockaddr>(),
                size_of::<SockaddrUnix>() as u32,
            ),
            None => (std::ptr::null::<libc::sockaddr>() as *mut libc::sockaddr, 0),
        };

        // println!("[Accept] Before GenSockaddr: {:?}", addr);
        // io::stdout().flush().unwrap();

        let ret_kernelfd = unsafe { libc::accept(vfd.underfd as i32, finalsockaddr, &mut addrlen as *mut u32) };

        if ret_kernelfd < 0 {
            // let errno = unsafe {
            //     *libc::__errno_location() 
            // } as i32;
            // let err = unsafe {
            //     libc::__errno_location()
            // };
            // let err_str = unsafe {
            //     libc::strerror(*err)
            // };
            // let err_msg = unsafe {
            //     CStr::from_ptr(err_str).to_string_lossy().into_owned()
            // };
            // println!("[Accept] Error message: {:?}", err_msg);
            // io::stdout().flush().unwrap();
            // println!("[Accept] errno: {:?}", errno);
            // io::stdout().flush().unwrap();
            let errno = get_errno();
            return handle_errno(errno, "accept");
        }

        // change the GenSockaddr type according to the sockaddr we received 
        // GenSockAddr will be modified after libc::accept returns 
        // So we only need to modify values in GenSockAddr, and rest of the things will be finished in dispatcher stage
        // println!("[Accept] After GenSockaddr: {:?}", addr);
        // println!("[Accept] finalsockaddr: {:?}", finalsockaddr);
        // io::stdout().flush().unwrap();

        if let Some(sockaddr) = addr {
            if let GenSockaddr::Unix(ref mut sockaddr_unix) = sockaddr{
                unsafe {
                    if std::slice::from_raw_parts(sockaddr_unix.sun_path.as_ptr() as *const u8, LIND_ROOT.len()) == LIND_ROOT.as_bytes() {
                        // Move ptr to exclue LIND_ROOT
                        let new_path_ptr = sockaddr_unix.sun_path.as_ptr().add(LIND_ROOT.len());
                
                        // sun_path in RawPOSIX will always be 108
                        let new_path_len = 108 - LIND_ROOT.len();
                
                        let mut temp_path = vec![0u8; sockaddr_unix.sun_path.len()];
                
                        std::ptr::copy_nonoverlapping(new_path_ptr, temp_path.as_mut_ptr(), new_path_len);
                
                        for i in 0..sockaddr_unix.sun_path.len() {
                            sockaddr_unix.sun_path[i] = 0;
                        }
                
                        std::ptr::copy_nonoverlapping(temp_path.as_ptr(), sockaddr_unix.sun_path.as_mut_ptr(), new_path_len);
                    }
                }
            }
        }

        let ret_virtualfd = fdtables::get_unused_virtual_fd(self.cageid, FDKIND_KERNEL, ret_kernelfd as u64, false, 0).unwrap();
        
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

        let (newnfds, mut real_readfds, mut real_writefds, mut real_errorfds, unrealset, mappingtable) 
            = fdtables::get_real_bitmasks_for_select(
                self.cageid,
                nfds as u64,
                orfds.copied(),
                owfds.copied(),
                oefds.copied(),
            ).unwrap();

        // libc select()
        // Ensured that null_mut is used if the Option is None for fd_set parameters.
        let ret = unsafe { 
            libc::select(
                newnfds as i32, 
                 real_readfds.as_mut().map_or(std::ptr::null_mut(), |fds| fds as *mut fd_set), 
                real_writefds.as_mut().map_or(std::ptr::null_mut(), |fds| fds as *mut fd_set), 
                real_errorfds.as_mut().map_or(std::ptr::null_mut(), |fds| fds as *mut fd_set), 
                &mut timeout as *mut timeval)
        };

        if ret < 0 {
            let errno = get_errno();
            return handle_errno(errno, "select");
        }

        // impipe select()
        let start_time = starttimer();

        let end_time = match rposix_timeout {
            Some(time) => time,
            None => RustDuration::MAX,
        };

        let mut return_code = 0;
        let mut unrealreadset = HashSet::new();
        let mut unrealwriteset = HashSet::new();

        loop {
            for (impfd_read, optinfo) in unrealset[0].iter() {
                if let Some(pipe_entry) = PIPE_TABLE.get(&optinfo) {
                    if pipe_entry.pipe.check_select_read() {
                        return_code = return_code + 1;
                        unrealreadset.insert(*impfd_read);
                    }
                }
            }

            for (impfd_write, optinfo) in unrealset[1].iter() {
                if let Some(pipe_entry) = PIPE_TABLE.get(&optinfo) {
                    if pipe_entry.pipe.check_select_write() {
                        return_code = return_code + 1;
                        unrealwriteset.insert(*impfd_write);
                    }
                }
            }

            for (impfd_err, optinfo) in unrealset[2].iter() {
                if let Some(pipe_entry) = PIPE_TABLE.get(&optinfo) {
                    // TODO
                }
            }

             // we break if there is any file descriptor ready
            // or timeout is reached
            if return_code != 0 || readtimer(start_time) > end_time {
                break;
            } else {
                // otherwise, check for signal and loop again
                if sigcheck() {
                    return syscall_error(Errno::EINTR, "poll", "interrupted function call");
                }
                // We yield to let other threads continue if we've found no ready descriptors
                lind_yield();
            }
        }
        // Revert result
        match fdtables::get_virtual_bitmasks_from_select_result(
            newnfds as u64,
            real_readfds,
            real_writefds,
            real_errorfds,
            unrealreadset,
            unrealwriteset,
            HashSet::new(),
            &mappingtable,
            // mappingtable,
        ) {
            Ok((_retnfds, retreadfds, retwritefds, reterrorfds)) => {
                if let Some(rfds) = readfds.as_mut() {
                    if let Some(ret_rfds) = retreadfds {
                        **rfds = ret_rfds;
                    } else {
                        // Clear the fd_set if result is None
                        unsafe { libc::FD_ZERO(&mut **rfds); } 
                    }
                }
    
                if let Some(wfds) = writefds.as_mut() {
                    if let Some(ret_wfds) = retwritefds {
                        **wfds = ret_wfds;
                    } else {
                        // Clear the fd_set if result is None
                        unsafe { libc::FD_ZERO(&mut **wfds); }
                    }
                }
    
                if let Some(efds) = errorfds.as_mut() {
                    if let Some(ret_efds) = reterrorfds {
                        **efds = ret_efds;
                    } else {
                        // Clear the fd_set if result is None
                        unsafe { libc::FD_ZERO(&mut **efds); }
                    }
                }
            },
            Err(e) => {
                panic!("");
            }
        }

        // Which should modify..?
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
        // optval: *mut u8,
        optval: &mut i32,
        // optlen: u32,
    ) -> i32 {
        let wrappedvfd = fdtables::translate_virtual_fd(self.cageid, virtual_fd as u64);
        if wrappedvfd.is_err() {
            return syscall_error(Errno::EBADF, "getsockopt", "Bad File Descriptor");
        }
        let vfd = wrappedvfd.unwrap();

        // let mut optlen: u32 = 4;
        let mut optlen: socklen_t = 4;

        // let ret = unsafe { libc::getsockopt(vfd.underfd as i32, level, optname, optval as *mut c_void, optlen as *mut u32) };
        let ret = unsafe { libc::getsockopt(vfd.underfd as i32, level, optname, optval as *mut c_int as *mut c_void, &mut optlen as *mut socklen_t) };
        if ret < 0 {
            // let err = unsafe {
            //     libc::__errno_location()
            // };
            // let err_str = unsafe {
            //     libc::strerror(*err)
            // };
            // let err_msg = unsafe {
            //     CStr::from_ptr(err_str).to_string_lossy().into_owned()
            // };
            // println!("[Getsockopt] Error message: {:?}", err_msg);
            // io::stdout().flush().unwrap();
            let errno = get_errno();
            return handle_errno(errno, "getsockopt");
        }
        

        // println!("[Getsockopt] optval: {:?}", optval);
        // io::stdout().flush().unwrap();
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
        let wrappedvfd = fdtables::translate_virtual_fd(self.cageid, virtual_fd as u64);
        if wrappedvfd.is_err() {
            return syscall_error(Errno::EBADF, "setsockopt", "Bad File Descriptor");
        }
        let vfd = wrappedvfd.unwrap();

        let ret = unsafe { 
            libc::setsockopt(vfd.underfd as i32, level, optname, optval as *mut c_void, optlen)
        };
        if ret < 0 {
            // let err = unsafe {
            //     libc::__errno_location()
            // };
            // let err_str = unsafe {
            //     libc::strerror(*err)
            // };
            // let err_msg = unsafe {
            //     CStr::from_ptr(err_str).to_string_lossy().into_owned()
            // };
            // println!("[Setsockopt] Error message: {:?}", err_msg);
            // io::stdout().flush().unwrap();
            let errno = get_errno();
            return handle_errno(errno, "setsockopt");
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
        let wrappedvfd = fdtables::translate_virtual_fd(self.cageid, virtual_fd as u64);
        if wrappedvfd.is_err() {
            return syscall_error(Errno::EBADF, "getpeername", "Bad File Descriptor");
        }
        let vfd = wrappedvfd.unwrap();
        
        let (finalsockaddr, mut addrlen) = match address {
            Some(GenSockaddr::V6(ref mut addrref6)) => (
                (addrref6 as *mut SockaddrV6).cast::<libc::sockaddr>(),
                size_of::<SockaddrV6>() as u32,
            ),
            Some(GenSockaddr::V4(ref mut addrref)) => (
                (addrref as *mut SockaddrV4).cast::<libc::sockaddr>(),
                size_of::<SockaddrV4>() as u32,
            ),
            Some(GenSockaddr::Unix(ref mut addrrefu)) => (
                (addrrefu as *mut SockaddrUnix).cast::<libc::sockaddr>(),
                size_of::<SockaddrUnix>() as u32,
            ),
            None => (std::ptr::null::<libc::sockaddr>() as *mut libc::sockaddr, 0),
        };

        // println!("[getpeername] addr BEFORE: {:?}", address);
        // println!("[getpeername] finalsockaddr BEFORE: {:?}", finalsockaddr);
        // io::stdout().flush().unwrap();

        let ret = unsafe { libc::getpeername(vfd.underfd as i32, finalsockaddr, &mut addrlen as *mut u32) };

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
            println!("[getpeername] Error message: {:?}", err_msg);
            
            let errno = get_errno();
            println!("[getpeername] Errno: {:?}", errno);
            io::stdout().flush().unwrap();
            return handle_errno(errno, "getpeername");
        }
        // println!("[getpeername] finalsockaddr After: {:?}", finalsockaddr);
        // io::stdout().flush().unwrap();

        if let Some(sockaddr) = address {
            if let GenSockaddr::Unix(ref mut sockaddr_unix) = sockaddr{
                unsafe {
                    if std::slice::from_raw_parts(sockaddr_unix.sun_path.as_ptr() as *const u8, LIND_ROOT.len()) == LIND_ROOT.as_bytes() {
                        // Move ptr to exclue LIND_ROOT
                        let new_path_ptr = sockaddr_unix.sun_path.as_ptr().add(LIND_ROOT.len());
                
                        // sun_path in RawPOSIX will always be 108
                        let new_path_len = 108 - LIND_ROOT.len();
                
                        let mut temp_path = vec![0u8; sockaddr_unix.sun_path.len()];
                
                        std::ptr::copy_nonoverlapping(new_path_ptr, temp_path.as_mut_ptr(), new_path_len);
                
                        for i in 0..sockaddr_unix.sun_path.len() {
                            sockaddr_unix.sun_path[i] = 0;
                        }
                
                        std::ptr::copy_nonoverlapping(temp_path.as_ptr(), sockaddr_unix.sun_path.as_mut_ptr(), new_path_len);
                    }
                }
            }
        }

        // println!("[getpeername] addr: {:?}", address);
        // io::stdout().flush().unwrap();

        ret
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
        let wrappedvfd = fdtables::translate_virtual_fd(self.cageid, virtual_fd as u64);
        if wrappedvfd.is_err() {
            return syscall_error(Errno::EBADF, "getsockname", "Bad File Descriptor");
        }
        let vfd = wrappedvfd.unwrap();

        let (finalsockaddr, mut addrlen) = match address {
            Some(GenSockaddr::V6(ref mut addrref6)) => (
                (addrref6 as *mut SockaddrV6).cast::<libc::sockaddr>(),
                size_of::<SockaddrV6>() as u32,
            ),
            Some(GenSockaddr::V4(ref mut addrref)) => (
                (addrref as *mut SockaddrV4).cast::<libc::sockaddr>(),
                size_of::<SockaddrV4>() as u32,
            ),
            Some(GenSockaddr::Unix(ref mut addrrefu)) => (
                (addrrefu as *mut SockaddrUnix).cast::<libc::sockaddr>(),
                size_of::<SockaddrUnix>() as u32,
            ),
            None => (std::ptr::null::<libc::sockaddr>() as *mut libc::sockaddr, 0),
        };

        let mut testlen = 128 as u32;
        // let ret = unsafe { libc::getsockname(vfd.underfd as i32, finalsockaddr, addrlen as *mut u32) };
        let ret = unsafe { libc::getsockname(vfd.underfd as i32, finalsockaddr, &mut testlen as *mut u32) };

        if ret < 0  {
            // let err = unsafe {
            //     libc::__errno_location()
            // };
            // let err_str = unsafe {
            //     libc::strerror(*err)
            // };
            // let err_msg = unsafe {
            //     CStr::from_ptr(err_str).to_string_lossy().into_owned()
            // };
            // println!("[getsockname] Error message: {:?}", err_msg);
            // println!("[getsockname] address: {:?}", address);
            // println!("[getsockname] finalsockaddr: {:?}", finalsockaddr);
            // io::stdout().flush().unwrap();
            let errno = get_errno();
            return handle_errno(errno, "getsockname");
        }

        ret
    }

    /*  
     *   gethostname() will return 0 when success and -1 when fail
     */
    pub fn gethostname_syscall(&self, name: *mut u8, len: isize) -> i32 {
        let ret = unsafe { libc::gethostname(name as *mut i8, len as usize) };
        if ret < 0 {
            let errno = get_errno();
            return handle_errno(errno, "gethostname");
        }
        ret
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
        /* 
        *   1. Get virfd list
        *   2. Get imp / real / invalid fd set list 
        *   3. For impipe
        *      For real fd
        */

        let mut virfdvec = Vec::with_capacity(virtual_fds.len());

        for vpoll in &mut *virtual_fds {
            let vfd = vpoll.fd as u64;
            virfdvec.push(vfd);
        }

        let (mut realfdvec, mut impvec, mut invalidfdvec, mut mappingtable) = fdtables::convert_virtualfds_to_real(self.cageid, virfdvec);
        


        // libc
        let mut libc_nfds = 0;
        let mut libc_pollfds: Vec<pollfd> = Vec::new();
        for &real_fd in &realfdvec {
            if let Some(&virtual_fd) = mappingtable.get(&real_fd) {
                // Find corresponding PollStruct in virtual_fds 
                if let Some(poll_struct) = virtual_fds.iter().find(|&ps| ps.fd == virtual_fd as i32) {
                    // Convert PollStruct to libc::pollfd
                    let libc_poll_struct = self.convert_to_libc_pollfd(poll_struct);
                    libc_pollfds.push(libc_poll_struct);
                    libc_nfds = libc_nfds + 1;
                }
            }
        }
        // For real fd, we call down to kernel
        if libc_nfds != 0 {
            let ret = unsafe { libc::poll(libc_pollfds.as_mut_ptr(), libc_nfds as u64, timeout) };
            if ret < 0 {
                // let err = unsafe {
                //     libc::__errno_location()
                // };
                // let err_str = unsafe {
                //     libc::strerror(*err)
                // };
                // let err_msg = unsafe {
                //     CStr::from_ptr(err_str).to_string_lossy().into_owned()
                // };
                // println!("[POLL] Error message: {:?}", err_msg);
                // println!("[POLL] kernel fd: {:?}", real_fd);
                // io::stdout().flush().unwrap();
                let errno = get_errno();
                return handle_errno(errno, "poll");
            }
            // Convert back to PollStruct
            for (i, libcpoll) in libc_pollfds.iter().enumerate() {
                if let Some(rposix_poll) = virtual_fds.get_mut(i) {
                    rposix_poll.revents = libcpoll.revents;
                }
            }
            
            return ret;
        }

        // In memory pipe
        let start_time = starttimer();
        let r_timeout = if timeout >= 0 {
            Some(RustDuration::from_millis(
                timeout as u64,
            ))
        } else {
            None
        };

        let end_time = match r_timeout {
            Some(time) => time,
            None => RustDuration::MAX,
        };

        let mut return_code = 0;

        loop {
            let mut event_count = 0;

            for (impfd, optinfo) in impvec.iter() {
                if let Some(pipe_entry) = PIPE_TABLE.get(&optinfo) {
                    //impipe_entry.perfdinfo as i32 & O_RDONLY != 0
                    if pipe_entry.isreader == true {
                        if pipe_entry.pipe.check_select_read() {
                            return_code = return_code + 1;
                            let mut r_pollstruct = virtual_fds.iter_mut().find(|rps| rps.fd == *impfd as i32).unwrap();
                            r_pollstruct.revents = libc::POLLIN;
                        }
                        
                    } else {
                        //impipe_entry.perfdinfo as i32 & O_WRONLY != 0
                        if pipe_entry.pipe.check_select_write() {
                            return_code = return_code + 1;
                            let mut r_pollstruct = virtual_fds.iter_mut().find(|rps| rps.fd == *impfd as i32).unwrap();
                            r_pollstruct.revents = libc::POLLOUT;
                        }
                        
                    }
                }
            }

             // we break if there is any file descriptor ready
            // or timeout is reached
            if return_code != 0 || readtimer(start_time) > end_time {
                break;
            } else {
                // otherwise, check for signal and loop again
                if sigcheck() {
                    return syscall_error(Errno::EINTR, "poll", "interrupted function call");
                }
                // We yield to let other threads continue if we've found no ready descriptors
                lind_yield();
            }
        }

        return return_code;
        
    }

    /* POLL()
    */
    fn convert_to_libc_pollfd(&self, poll_struct: &PollStruct) -> pollfd {
        pollfd {
            fd: poll_struct.fd,
            events: poll_struct.events,
            revents: poll_struct.revents,
        }
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
            // let err = unsafe {
            //     libc::__errno_location()
            // };
            // let err_str = unsafe {
            //     libc::strerror(*err)
            // };
            // let err_msg = unsafe {
            //     CStr::from_ptr(err_str).to_string_lossy().into_owned()
            // };
            // println!("Error message: {:?}", err_msg);
            // println!("[EPOLL] size: {:?}", size);
            // println!("[EPOLL] kernelfd: {:?}", kernel_fd);
            // io::stdout().flush().unwrap();
            let errno = get_errno();
            return handle_errno(errno, "epoll_create");
        }

        // Get the virtual epfd
        let virtual_epfd = fdtables::get_unused_virtual_fd(self.cageid, FDKIND_KERNEL, kernel_fd as u64, false, 0).unwrap();
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
        let wrappedepfd = fdtables::translate_virtual_fd(self.cageid, virtual_epfd as u64);
        let wrappedvfd = fdtables::translate_virtual_fd(self.cageid, virtual_fd as u64);
        if wrappedvfd.is_err() || wrappedepfd.is_err() {
            return syscall_error(Errno::EBADF, "epoll", "Bad File Descriptor");
        }

        let vepfd = wrappedepfd.unwrap();
        let vfd = wrappedvfd.unwrap();
        // EpollEvent conversion
        let event = epollevent.events;
        let mut epoll_event = epoll_event {
            events: event,
            u64: vfd.underfd as u64,
        };

        let ret = unsafe { libc::epoll_ctl(vepfd.underfd as i32, op, vfd.underfd as i32, &mut epoll_event) };
        if ret < 0 {
            // let err = unsafe {
            //     libc::__errno_location()
            // };
            // let err_str = unsafe {
            //     libc::strerror(*err)
            // };
            // let err_msg = unsafe {
            //     CStr::from_ptr(err_str).to_string_lossy().into_owned()
            // };
            // println!("[epoll_ctl] Error message: {:?}", err_msg);
            // io::stdout().flush().unwrap();
            let errno = get_errno();
            return handle_errno(errno, "epoll_ctl");
        }

        // Update the virtual list -- but we only handle the non-real fd case
        //  try_epoll_ctl will directly return a real fd in libc case
        //  - maybe we could create a new mapping table to handle the mapping relationship..?
        //      ceate inside the fdtable interface? or we could handle inside rawposix..?
        
        // Update the mapping table for epoll
        if op == libc::EPOLL_CTL_DEL {
            let mut epollmapping = REAL_EPOLL_MAP.lock();
            if let Some(fdmap) = epollmapping.get_mut(&(vepfd.underfd as u64)) {
                if fdmap.remove(&(vfd.underfd as i32)).is_some() {
                    if fdmap.is_empty() {
                        epollmapping.remove(&(vepfd.underfd as u64));
                    }
                    return ret;
                }
            }
        } else {
            let mut epollmapping = REAL_EPOLL_MAP.lock();
            epollmapping.entry(vepfd.underfd as u64).or_insert_with(HashMap::new).insert(vfd.underfd as i32, virtual_fd as u64);
            return ret;
        }

        // [TODO]
        // should be op not support
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
        let wrappedepfd = fdtables::translate_virtual_fd(self.cageid, virtual_epfd as u64);
        if wrappedepfd.is_err() {
            return syscall_error(Errno::EBADF, "epoll_wait", "Bad File Descriptor");
        }
        let vepfd = wrappedepfd.unwrap();
        
        let mut kernel_events: Vec<epoll_event> = Vec::with_capacity(maxevents as usize);

        // Should always be null value before we call libc::epoll_wait
        kernel_events.push(
            epoll_event {
                events: 0,
                u64: 0,
            }
        );

        let ret = unsafe { libc::epoll_wait(vepfd.underfd as i32, kernel_events.as_mut_ptr(), maxevents, timeout as i32) };
        if ret < 0 {
            // let err = unsafe {
            //     libc::__errno_location()
            // };
            // let err_str = unsafe {
            //     libc::strerror(*err)
            // };
            // let err_msg = unsafe {
            //     CStr::from_ptr(err_str).to_string_lossy().into_owned()
            // };
            // println!("[epoll_wait] Error message: {:?}", err_msg);
            // io::stdout().flush().unwrap();
            let errno = get_errno();
            return handle_errno(errno, "epoll_wait");
        }

        // Convert back to rustposix's data structure
        // Loop over virtual_epollfd to find corresponding mapping relationship between kernel fd and virtual fd
        for i in 0..ret as usize {

            let ret_kernelfd = kernel_events[i].u64;
            let epollmapping = REAL_EPOLL_MAP.lock();
            let ret_virtualfd = epollmapping.get(&(vepfd.underfd as u64)).and_then(|kernel_map| kernel_map.get(&(ret_kernelfd as i32)).copied());

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
        if ret < 0 {
            let errno = get_errno();
            return handle_errno(errno, "sockpair");
        }

        let ksv_1 = kernel_socket_vector[0];
        let ksv_2 = kernel_socket_vector[1];
        let vsv_1 = fdtables::get_unused_virtual_fd(self.cageid, FDKIND_KERNEL, ksv_1 as u64, false, 0).unwrap();
        let vsv_2 = fdtables::get_unused_virtual_fd(self.cageid, FDKIND_KERNEL, ksv_2 as u64, false, 0).unwrap();
        virtual_socket_vector.sock1 = vsv_1 as i32;
        virtual_socket_vector.sock2 = vsv_2 as i32;
        return 0;
    }

    /*
    *   Get result back from libc::getifaddrs and fill the content of name field into a buf 
    *   as rustposix, so that i don’t need to change the dispatcher interface
    */
    pub fn getifaddrs_syscall(&self, buf: *mut u8, count: usize) -> i32 {
        let mut ifaddr: *mut ifaddrs = ptr::null_mut();

        unsafe {
            if getifaddrs(&mut ifaddr) < 0 {
                // let err = libc::__errno_location();
                // let err_str = libc::strerror(*err);
                // let err_msg = CStr::from_ptr(err_str).to_string_lossy().into_owned();
                // println!("Error message: {:?}", err_msg);
                // io::stdout().flush().unwrap();
                let errno = get_errno();
                return handle_errno(errno, "getifaddrs");
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

}


