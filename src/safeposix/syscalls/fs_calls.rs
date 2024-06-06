#![allow(dead_code)]

use super::fs_constants;
// File system related system calls
use super::fs_constants::*;
use super::sys_constants::*;
use crate::interface;
use crate::interface::FSData;
use crate::safeposix::cage::Errno::EINVAL;
use crate::safeposix::cage::*;
use crate::safeposix::filesystem::convpath;
use crate::safeposix::filesystem::normpath;
// use crate::safeposix::filesystem::*;
// use crate::safeposix::net::NET_METADATA;
use crate::safeposix::shm::*;
use crate::interface::ShmidsStruct;
use crate::interface::StatData;

use libc::*;
use std::io::stdout;
use std::os::unix::io::RawFd;
use std::io::{self, Write};
use std::ffi::CStr;
use std::ffi::CString;
use std::ptr;
use std::mem;

use crate::example_grates::dashmapvecglobal::*;

static LIND_ROOT: &str = "/home/lind/lind_project/src/safeposix-rust/tmp";

/* 
*   We will receive parameters with type u64 by default, then we will do type conversion inside
*   of each syscall
*   
*   [Concerns]
*   - cloexec in get_unused_virtual_fd()..?
*   - there's no getdents() API in rust libc
*   
*/

impl Cage {
    //------------------------------------OPEN SYSCALL------------------------------------
    /* 
    *   Open will return a file descriptor 
    *   Mapping a new virtual fd and kernel fd that libc::socket returned
    *   Then return virtual fd
    */
    pub fn open_syscall(&self, path: &str, oflag: i32, mode: u32) -> i32 {

        // Convert data type from &str into *const i8
        // let c_path = CString::new(path).unwrap();
        let relpath = normpath(convpath(path), self);
        let relative_path = relpath.to_str().unwrap();
        let full_path = format!("{}{}", LIND_ROOT, relative_path);
        let c_path = CString::new(full_path).unwrap();

        let kernel_fd = unsafe { libc::open(c_path.as_ptr(), oflag, mode) };

        // if kernel_fd < 0 {
        //     return -1;
        // }
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
            println!("errno: {:?}", err);
            println!("Error message: {:?}", err_msg);
            println!("c_path: {:?}", c_path);
            io::stdout().flush().unwrap();
            return -1;
        }

        let virtual_fd = get_unused_virtual_fd(self.cageid, kernel_fd as u64, false, 0).unwrap();
        virtual_fd as i32
    }

    //------------------MKDIR SYSCALL------------------
    /*
    *   mkdir() will return 0 when success and -1 when fail 
    */
    pub fn mkdir_syscall(&self, path: &str, mode: u32) -> i32 {
        // Convert data type from &str into *const i8
        // let c_path = CString::new(path).expect("CString::new failed");
        let relpath = normpath(convpath(path), self);
        let relative_path = relpath.to_str().unwrap();
        let full_path = format!("{}{}", LIND_ROOT, relative_path);
        let c_path = CString::new(full_path).unwrap();
        
        unsafe {
            libc::mkdir(c_path.as_ptr(), mode)
        }
    }

    //------------------MKNOD SYSCALL------------------
    /*
    *   mknod() will return 0 when success and -1 when fail 
    */
    pub fn mknod_syscall(&self, path: &str, mode: u32, dev: u64) -> i32 {
        // Convert data type from &str into *const i8
        // let c_path = CString::new(path).expect("CString::new failed");
        let relpath = normpath(convpath(path), self);
        let relative_path = relpath.to_str().unwrap();
        let full_path = format!("{}{}", LIND_ROOT, relative_path);
        let c_path = CString::new(full_path).unwrap();
        unsafe {
            libc::mknod(c_path.as_ptr(), mode, dev)
        }
    }

    //------------------------------------LINK SYSCALL------------------------------------
    /*
    *   link() will return 0 when success and -1 when fail 
    */
    pub fn link_syscall(&self, oldpath: &str, newpath: &str) -> i32 {
        // Convert data type from &str into *const i8
        let old_cpath = CString::new(oldpath).expect("CString::new failed");
        let new_cpath = CString::new(newpath).expect("CString::new failed");
        unsafe {
            libc::link(old_cpath.as_ptr(), new_cpath.as_ptr())
        }
    }

    //------------------------------------UNLINK SYSCALL------------------------------------
    /*
    *   unlink() will return 0 when success and -1 when fail 
    */
    pub fn unlink_syscall(&self, path: &str) -> i32 {
        let (path_c, _, _) = path.to_string().into_raw_parts();
        unsafe {
            libc::unlink(path_c as *const i8)
        }
    }

    //------------------------------------CREAT SYSCALL------------------------------------
    /*
    *   creat() will return fd when success and -1 when fail 
    */
    pub fn creat_syscall(&self, path: &str, mode: u32) -> i32 {
        // let c_path = CString::new(path).expect("CString::new failed");
        let relpath = normpath(convpath(path), self);
        let relative_path = relpath.to_str().unwrap();
        let full_path = format!("{}{}", LIND_ROOT, relative_path);
        let c_path = CString::new(full_path).unwrap();

        let kernel_fd = unsafe {
            libc::creat(c_path.as_ptr(), mode)
        };
        let virtual_fd = get_unused_virtual_fd(self.cageid, kernel_fd as u64, false, 0).unwrap();
        virtual_fd as i32
    }

    //------------------------------------STAT SYSCALL------------------------------------
    /*
    *   stat() will return 0 when success and -1 when fail 
    */
    // pub fn stat_syscall(&self, path: &str, statbuf: &mut stat) -> i32 {
    //     // let c_path = CString::new(path).expect("CString::new failed");
    //     let relpath = normpath(convpath(path), self);
    //     let relative_path = relpath.to_str().unwrap();
    //     let full_path = format!("{}{}", LIND_ROOT, relative_path);
    //     let c_path = CString::new(full_path).unwrap();
    //     unsafe {
    //         libc::stat(c_path.as_ptr(), statbuf)
    //     }
    // }
    pub fn stat_syscall(&self, path: &str, rposix_statbuf: &mut StatData) -> i32 {
        let relpath = normpath(convpath(path), self);
        let relative_path = relpath.to_str().unwrap();
        let full_path = format!("{}{}", LIND_ROOT, relative_path);
        let c_path = CString::new(full_path).unwrap();

        // Declare statbuf by ourselves 
        let mut libc_statbuf: stat = unsafe { std::mem::zeroed() };
        let libcret = unsafe {
            libc::stat(c_path.as_ptr(), &mut libc_statbuf)
        };
        
        if libcret < 0 {
            let err = unsafe {
                libc::__errno_location()
            };
            let err_str = unsafe {
                libc::strerror(*err)
            };
            let err_msg = unsafe {
                CStr::from_ptr(err_str).to_string_lossy().into_owned()
            };
            println!("errno: {:?}", err);
            println!("Error message: {:?}", err_msg);
            println!("c_path: {:?}", c_path);
            io::stdout().flush().unwrap();
            return -1;
        }
        
        if libcret == 0 {
            rposix_statbuf.st_atim = libc_statbuf.st_atime;
            rposix_statbuf.st_blksize = libc_statbuf.st_blksize;
            rposix_statbuf.st_blocks = libc_statbuf.st_blocks;
            rposix_statbuf.st_ctim = libc_statbuf.st_ctime;
            rposix_statbuf.st_dev = libc_statbuf.st_dev;
            rposix_statbuf.st_gid = libc_statbuf.st_gid;
            rposix_statbuf.st_ino = libc_statbuf.st_ino;
            rposix_statbuf.st_mode = libc_statbuf.st_mode;
            rposix_statbuf.st_mtim = libc_statbuf.st_mtime;
            rposix_statbuf.st_nlink = libc_statbuf.st_nlink;
            rposix_statbuf.st_rdev = libc_statbuf.st_rdev;
            rposix_statbuf.st_size = libc_statbuf.st_size;
            rposix_statbuf.st_uid = libc_statbuf.st_uid;
            
        }
        libcret
    }

    //------------------------------------FSTAT SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   fstat() will return 0 when success and -1 when fail 
    */
    // pub fn fstat_syscall(&self, virtual_fd: i32, statbuf: &mut stat) -> i32 {
    //     let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
    //     unsafe {
    //         libc::fstat(kernel_fd, statbuf)
    //     }
    // }
    pub fn fstat_syscall(&self, virtual_fd: i32, rposix_statbuf: &mut StatData) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        // Declare statbuf by ourselves 
        let mut libc_statbuf: stat = unsafe { std::mem::zeroed() };
        let libcret = unsafe {
        libc::fstat(kernel_fd as i32, &mut libc_statbuf)
        };
        
        if libcret == 0 {
            rposix_statbuf.st_atim = libc_statbuf.st_atime;
            rposix_statbuf.st_blksize = libc_statbuf.st_blksize;
            rposix_statbuf.st_blocks = libc_statbuf.st_blocks;
            rposix_statbuf.st_ctim = libc_statbuf.st_ctime;
            rposix_statbuf.st_dev = libc_statbuf.st_dev;
            rposix_statbuf.st_gid = libc_statbuf.st_gid;
            rposix_statbuf.st_ino = libc_statbuf.st_ino;
            rposix_statbuf.st_mode = libc_statbuf.st_mode;
            rposix_statbuf.st_mtim = libc_statbuf.st_mtime;
            rposix_statbuf.st_nlink = libc_statbuf.st_nlink;
            rposix_statbuf.st_rdev = libc_statbuf.st_rdev;
            rposix_statbuf.st_size = libc_statbuf.st_size;
            rposix_statbuf.st_uid = libc_statbuf.st_uid;
        }
        libcret
    }

    //------------------------------------STATFS SYSCALL------------------------------------
    /*
    *   statfs() will return 0 when success and -1 when fail 
    */
    pub fn statfs_syscall(&self, path: &str, rposix_databuf: &mut FSData) -> i32 {
        let relpath = normpath(convpath(path), self);
        let relative_path = relpath.to_str().unwrap();
        let full_path = format!("{}{}", LIND_ROOT, relative_path);
        let c_path = CString::new(full_path).unwrap();

        let mut libc_databuf: statfs = unsafe { mem::zeroed() };
        let libcret = unsafe {
            libc::statfs(c_path.as_ptr(), &mut libc_databuf)
        };
        if libcret == 0 {
            rposix_databuf.f_bavail = libc_databuf.f_bavail;
            rposix_databuf.f_bfree = libc_databuf.f_bfree;
            rposix_databuf.f_blocks = libc_databuf.f_blocks;
            rposix_databuf.f_bsize = libc_databuf.f_bsize;
            rposix_databuf.f_ffiles = libc_databuf.f_ffree;
            rposix_databuf.f_files = libc_databuf.f_files;
            rposix_databuf.f_fsid = libc_databuf.f_fsid;
        }
        libcret
    }

    //------------------------------------FSTATFS SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   fstatfs() will return 0 when success and -1 when fail 
    */
    pub fn fstatfs_syscall(&self, virtual_fd: i32, rposix_databuf: &mut FSData) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        
        let mut libc_databuf: statfs = unsafe { mem::zeroed() };
        let libcret = unsafe {
            libc::fstatfs(kernel_fd as i32, &mut libc_databuf)
        };
        if libcret == 0 {
            rposix_databuf.f_bavail = libc_databuf.f_bavail;
            rposix_databuf.f_bfree = libc_databuf.f_bfree;
            rposix_databuf.f_blocks = libc_databuf.f_blocks;
            rposix_databuf.f_bsize = libc_databuf.f_bsize;
            rposix_databuf.f_ffiles = libc_databuf.f_ffree;
            rposix_databuf.f_files = libc_databuf.f_files;
            rposix_databuf.f_fsid = libc_databuf.f_fsid;
        }
        libcret
    }

    //------------------------------------READ SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   read() will return:
    *   - the number of bytes read is returned, success
    *   - -1, fail 
    */
    pub fn read_syscall(&self, virtual_fd: i32, readbuf: *mut u8, count: usize) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        let ret = unsafe {
            libc::read(kernel_fd as i32, readbuf as *mut c_void, count) as i32
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
            println!("errno: {:?}", err);
            println!("Error message: {:?}", err_msg);
            println!("kernel_fd: {:?}", kernel_fd);
            io::stdout().flush().unwrap();
            return -1;
        }
        ret
    }

    //------------------------------------PREAD SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   pread() will return:
    *   - the number of bytes read is returned, success
    *   - -1, fail 
    */
    pub fn pread_syscall(&self, virtual_fd: i32, buf: *mut u8, count: usize, offset: i64) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe {
            libc::pread(kernel_fd as i32, buf as *mut c_void, count, offset) as i32
        }
    }

    //------------------------------------WRITE SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   write() will return:
    *   - the number of bytes writen is returned, success
    *   - -1, fail 
    */
    pub fn write_syscall(&self, virtual_fd: i32, buf: *const u8, count: usize) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe {
            libc::write(kernel_fd as i32, buf as *const c_void, count) as i32
        }
    }

    //------------------------------------PWRITE SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   pwrite() will return:
    *   - the number of bytes read is returned, success
    *   - -1, fail 
    */
    pub fn pwrite_syscall(&self, virtual_fd: i32, buf: *const u8, count: usize, offset: i64) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe {
            libc::pwrite(kernel_fd as i32, buf as *const c_void, count, offset) as i32
        }
    }

    //------------------------------------LSEEK SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   lseek() will return:
    *   -  the resulting offset location as measured in bytes from the beginning of the file
    *   - -1, fail 
    */
    pub fn lseek_syscall(&self, virtual_fd: i32, offset: isize, whence: i32) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe {
            libc::lseek(kernel_fd as i32, offset as i64, whence) as i32
        }
    }

    //------------------------------------ACCESS SYSCALL------------------------------------
    /*
    *   access() will return 0 when sucess, -1 when fail 
    */
    pub fn access_syscall(&self, path: &str, amode: i32) -> i32 {
        // let c_path = CString::new(path).expect("CString::new failed");
        let relpath = normpath(convpath(path), self);
        let relative_path = relpath.to_str().unwrap();
        let full_path = format!("{}{}", LIND_ROOT, relative_path);
        let c_path = CString::new(full_path).unwrap();
        unsafe {
            libc::access(c_path.as_ptr(), amode)
        }
    }

    //------------------------------------FCHDIR SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   fchdir() will return 0 when sucess, -1 when fail 
    */
    pub fn fchdir_syscall(&self, virtual_fd: i32) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe {
            libc::fchdir(kernel_fd as i32)
        }
    }

    //------------------------------------CHDIR SYSCALL------------------------------------
    /*
    *   chdir() will return 0 when sucess, -1 when fail 
    */
    pub fn chdir_syscall(&self, path: &str) -> i32 {
        let truepath = normpath(convpath(path), self);
        
        //at this point, syscall isn't an error
        let mut cwd_container = self.cwd.write();

        *cwd_container = interface::RustRfc::new(truepath);
        0 
    }

    //------------------------------------DUP & DUP2 SYSCALLS------------------------------------
    /* 
    *   dup() / dup2() will return a file descriptor 
    *   Mapping a new virtual fd and kernel fd that libc::dup returned
    *   Then return virtual fd
    */
    pub fn dup_syscall(&self, virtual_fd: i32, _start_desc: Option<i32>) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        let ret_kernelfd = unsafe{ libc::dup(kernel_fd as i32) };
        let ret_virtualfd = get_unused_virtual_fd(self.cageid, ret_kernelfd as u64, false, 0).unwrap();
        ret_virtualfd as i32
    }

    /* 
    */
    pub fn dup2_syscall(&self, old_virtualfd: i32, new_virtualfd: i32) -> i32 {
        let old_kernelfd = translate_virtual_fd(self.cageid, old_virtualfd as u64).unwrap();
        let new_kernelfd = unsafe {
            libc::dup(old_kernelfd as i32)
        };
        // Map new kernel fd with provided kernel fd
        let ret_kernelfd = unsafe{ libc::dup2(old_kernelfd as i32, new_kernelfd) };
        let optinfo = get_optionalinfo(self.cageid, old_virtualfd as u64).unwrap();
        println!("ret_kernelfd: {:?}\nnew_kernelfd: {:?}", ret_kernelfd, new_virtualfd);
        io::stdout().flush().unwrap();
        let _ = get_specific_virtual_fd(self.cageid, new_virtualfd as u64, new_kernelfd as u64, false, optinfo).unwrap();
        new_virtualfd
    }

    //------------------------------------CLOSE SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   close() will return 0 when sucess, -1 when fail 
    */
    pub fn close_syscall(&self, virtual_fd: i32) -> i32 {
        match close_virtualfd(self.cageid, virtual_fd as u64) {
            Ok(()) => {
                return 0;
            }
            Err(_) => {
                return -1;
            }
        }
        
    }

    

    //------------------------------------FCNTL SYSCALL------------------------------------
    /*
    *   For a successful call, the return value depends on the operation:

       F_DUPFD
              The new file descriptor.

       F_GETFD
              Value of file descriptor flags.

       F_GETFL
              Value of file status flags.

       F_GETLEASE
              Type of lease held on file descriptor.

       F_GETOWN
              Value of file descriptor owner.

       F_GETSIG
              Value of signal sent when read or write becomes possible,
              or zero for traditional SIGIO behavior.

       F_GETPIPE_SZ, F_SETPIPE_SZ
              The pipe capacity.

       F_GET_SEALS
              A bit mask identifying the seals that have been set for
              the inode referred to by fd.

       All other commands
              Zero.

       On error, -1 is returned 
    */
    pub fn fcntl_syscall(&self, virtual_fd: i32, cmd: i32, arg: i32) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        if cmd == libc::F_DUPFD {
            let new_kernelfd = unsafe { libc::fcntl(kernel_fd as i32, cmd, arg) };
            // Get status
            let new_virtualfd = get_unused_virtual_fd(self.cageid, new_kernelfd as u64, false, 0).unwrap();
            return new_virtualfd as i32;
        }
        unsafe { libc::fcntl(kernel_fd as i32, cmd, arg) }
    }

    //------------------------------------IOCTL SYSCALL------------------------------------
    /*
    *   The third argument is an untyped pointer to memory.  It's traditionally char *argp 
    *   (from the days before void * was valid C), and will be so named for this discussion.
    *   ioctl() will return 0 when success and -1 when fail. 
    *   Note: A few ioctl() requests use the return value as an output parameter and return 
    *   a nonnegative value on success.
    */
    pub fn ioctl_syscall(&self, virtual_fd: i32, request: u64, ptrunion: *mut u8) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe { libc::ioctl(kernel_fd as i32, request, ptrunion as *mut c_void) }
    }


    //------------------------------------CHMOD SYSCALL------------------------------------
    /*
    *   chmod() will return 0 when success and -1 when fail 
    */
    pub fn chmod_syscall(&self, path: &str, mode: u32) -> i32 {
        // let c_path = CString::new(path).expect("CString::new failed");
        let relpath = normpath(convpath(path), self);
        let relative_path = relpath.to_str().unwrap();
        let full_path = format!("{}{}", LIND_ROOT, relative_path);
        let c_path = CString::new(full_path).unwrap();
        unsafe {
            libc::chmod(c_path.as_ptr(), mode)
        }
    }

    //------------------------------------FCHMOD SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   fchmod() will return 0 when sucess, -1 when fail 
    */
    pub fn fchmod_syscall(&self, virtual_fd: i32, mode: u32) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe {
            libc::fchmod(kernel_fd as i32, mode)
        }
    }

    //------------------------------------MMAP SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   mmap() will return:
    *   - a pointer to the mapped area, success
    *   - -1, fail
    */
    pub fn mmap_syscall(
        &self,
        addr: *mut u8,
        len: usize,
        prot: i32,
        flags: i32,
        virtual_fd: i32,
        off: i64,
    ) -> i32 {
        if virtual_fd != -1 {
            let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
            let ret = unsafe {
                ((libc::mmap(addr as *mut c_void, len, prot, flags, kernel_fd as i32, off) as i64) 
                    & 0xffffffff) as i32
            };
            return ret;
        }
        
        // Do type conversion to translate from c_void into i32
        unsafe {
            ((libc::mmap(addr as *mut c_void, len, prot, flags, -1, off) as i64) 
                & 0xffffffff) as i32
        }
    }

    //------------------------------------MUNMAP SYSCALL------------------------------------
    /*
    *   munmap() will return:
    *   - 0, success
    *   - -1, fail
    */
    pub fn munmap_syscall(&self, addr: *mut u8, len: usize) -> i32 {
        unsafe {
            libc::munmap(addr as *mut c_void, len)
        }
    }

    //------------------------------------FLOCK SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   flock() will return 0 when sucess, -1 when fail 
    */
    pub fn flock_syscall(&self, virtual_fd: i32, operation: i32) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe {
            libc::flock(kernel_fd as i32, operation)
        }
    }

    //------------------RMDIR SYSCALL------------------
    /*
    *   rmdir() will return 0 when sucess, -1 when fail 
    */
    pub fn rmdir_syscall(&self, path: &str) -> i32 {
        // let c_path = CString::new(path).expect("CString::new failed");
        let relpath = normpath(convpath(path), self);
        let relative_path = relpath.to_str().unwrap();
        let full_path = format!("{}{}", LIND_ROOT, relative_path);
        let c_path = CString::new(full_path).unwrap();
        unsafe {
            libc::rmdir(c_path.as_ptr())
        }
    }

    //------------------RENAME SYSCALL------------------
    /*
    *   rename() will return 0 when sucess, -1 when fail 
    */
    pub fn rename_syscall(&self, oldpath: &str, newpath: &str) -> i32 {
        let old_cpath = CString::new(oldpath).expect("CString::new failed");
        let new_cpath = CString::new(newpath).expect("CString::new failed");
        unsafe {
            libc::rename(old_cpath.as_ptr(), new_cpath.as_ptr())
        }
    }

    //------------------------------------FSYNC SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   fsync() will return 0 when sucess, -1 when fail 
    */
    pub fn fsync_syscall(&self, virtual_fd: i32) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe {
            libc::fsync(kernel_fd as i32)
        }
    }

    //------------------------------------FDATASYNC SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   fdatasync() will return 0 when sucess, -1 when fail 
    */
    pub fn fdatasync_syscall(&self, virtual_fd: i32) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe {
            libc::fdatasync(kernel_fd as i32)
        }
    }

    //------------------------------------SYNC_FILE_RANGE SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   sync_file_range() will return 0 when sucess, -1 when fail 
    */
    pub fn sync_file_range_syscall(
        &self,
        virtual_fd: i32,
        offset: isize,
        nbytes: isize,
        flags: u32,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe {
            libc::sync_file_range(kernel_fd as i32, offset as i64, nbytes as i64, flags)
        }
    }

    //------------------FTRUNCATE SYSCALL------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   ftruncate() will return 0 when sucess, -1 when fail 
    */
    pub fn ftruncate_syscall(&self, virtual_fd: i32, length: isize) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd as u64).unwrap();
        unsafe {
            libc::ftruncate(kernel_fd as i32, length as i64)
        }
    }

    //------------------TRUNCATE SYSCALL------------------
    /*
    *   truncate() will return 0 when sucess, -1 when fail 
    */
    pub fn truncate_syscall(&self, path: &str, length: isize) -> i32 {
        // let c_path = CString::new(path).expect("CString::new failed");
        let relpath = normpath(convpath(path), self);
        let relative_path = relpath.to_str().unwrap();
        let full_path = format!("{}{}", LIND_ROOT, relative_path);
        let c_path = CString::new(full_path).unwrap();
        unsafe {
            libc::truncate(c_path.as_ptr(), length as i64)
        }
    }

    //------------------PIPE SYSCALL------------------
    /*
    *   When using the rust libc, a pipe file descriptor (pipefd) is typically an array 
    *   containing two integers. This array is populated by the pipe system call, with one 
    *   integer for the read end and the other for the write end.
    *
    *   pipe() will return 0 when sucess, -1 when fail 
    */
    pub fn pipe_syscall(&self, pipefd: &mut PipeArray) -> i32 {
        let mut kernel_fds = [0; 2];
        
        let ret = unsafe { libc::pipe(kernel_fds.as_mut_ptr() as *mut i32) };
        pipefd.readfd = get_unused_virtual_fd(self.cageid, kernel_fds[0], false, 0).unwrap() as i32;
        pipefd.writefd = get_unused_virtual_fd(self.cageid, kernel_fds[1], false, 0).unwrap() as i32;

        return ret;
    }

    pub fn pipe2_syscall(&self, pipefd: &mut PipeArray, flags: i32) -> i32 {
        let mut kernel_fds:[i32; 2] = [0; 2];
        
        let ret = unsafe { libc::pipe2(kernel_fds.as_mut_ptr() as *mut i32, flags as i32) };

        if flags == libc::O_CLOEXEC {
            pipefd.readfd = get_unused_virtual_fd(self.cageid, kernel_fds[0], true, 0).unwrap() as i32;
            pipefd.writefd = get_unused_virtual_fd(self.cageid, kernel_fds[1], true, 0).unwrap() as i32;
        } else {
            pipefd.readfd = get_unused_virtual_fd(self.cageid, kernel_fds[0], false, 0).unwrap() as i32;
            pipefd.writefd = get_unused_virtual_fd(self.cageid, kernel_fds[1], false, 0).unwrap() as i32;
        }

        return ret;
    }

    //------------------GETDENTS SYSCALL------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   getdents() will return:
    *   - the number of bytes read is returned, success
    *   - 0, EOF
    *   - -1, fail 
    */
    // pub fn getdents_syscall(&self, virtual_fd: u64, dirp: *mut u8, bufsize: u64) -> i32 {
    //     let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
    //     unsafe {
    //     }
    // }

    //------------------------------------GETCWD SYSCALL------------------------------------
    /*
    *   getcwd() will return:
    *   - a pointer to a string containing the pathname of the current working directory, success
    *   - null, fail 
    */
    pub fn getcwd_syscall(&self, buf: *mut u8, bufsize: u32) -> i32 {
        let cwd_container = self.cwd.read();
        let path = cwd_container.to_str().unwrap();
        if path.len() >= bufsize as usize {
            return -1;
        }
        unsafe {
            ptr::copy(path.as_ptr(), buf, path.len());
            *buf.add(path.len()) = 0;
        }
        0
    }

    //------------------SHMHELPERS----------------------

    pub fn rev_shm_find_index_by_addr(rev_shm: &Vec<(u32, i32)>, shmaddr: u32) -> Option<usize> {
        for (index, val) in rev_shm.iter().enumerate() {
            if val.0 == shmaddr as u32 {
                return Some(index);
            }
        }
        None
    }

    pub fn rev_shm_find_addrs_by_shmid(rev_shm: &Vec<(u32, i32)>, shmid: i32) -> Vec<u32> {
        let mut addrvec = Vec::new();
        for val in rev_shm.iter() {
            if val.1 == shmid as i32 {
                addrvec.push(val.0);
            }
        }

        return addrvec;
    }

    pub fn search_for_addr_in_region(
        rev_shm: &Vec<(u32, i32)>,
        search_addr: u32,
    ) -> Option<(u32, i32)> {
        let metadata = &SHM_METADATA;
        for val in rev_shm.iter() {
            let addr = val.0;
            let shmid = val.1;
            if let Some(segment) = metadata.shmtable.get_mut(&shmid) {
                let range = addr..(addr + segment.size as u32);
                if range.contains(&search_addr) {
                    return Some((addr, shmid));
                }
            }
        }
        None
    }

    //------------------SHMGET SYSCALL------------------

    pub fn shmget_syscall(&self, key: i32, size: usize, shmflg: i32) -> i32 {
        if key == IPC_PRIVATE {
            return syscall_error(Errno::ENOENT, "shmget", "IPC_PRIVATE not implemented");
        }
        let shmid: i32;
        let metadata = &SHM_METADATA;

        match metadata.shmkeyidtable.entry(key) {
            interface::RustHashEntry::Occupied(occupied) => {
                if (IPC_CREAT | IPC_EXCL) == (shmflg & (IPC_CREAT | IPC_EXCL)) {
                    return syscall_error(
                        Errno::EEXIST,
                        "shmget",
                        "key already exists and IPC_CREAT and IPC_EXCL were used",
                    );
                }
                shmid = *occupied.get();
            }
            interface::RustHashEntry::Vacant(vacant) => {
                if 0 == (shmflg & IPC_CREAT) {
                    return syscall_error(
                        Errno::ENOENT,
                        "shmget",
                        "tried to use a key that did not exist, and IPC_CREAT was not specified",
                    );
                }

                if (size as u32) < SHMMIN || (size as u32) > SHMMAX {
                    return syscall_error(
                        Errno::EINVAL,
                        "shmget",
                        "Size is less than SHMMIN or more than SHMMAX",
                    );
                }

                shmid = metadata.new_keyid();
                vacant.insert(shmid);
                let mode = (shmflg & 0x1FF) as u16; // mode is 9 least signficant bits of shmflag, even if we dont really do anything with them

                let segment = new_shm_segment(
                    key,
                    size,
                    self.cageid as u32,
                    DEFAULT_UID,
                    DEFAULT_GID,
                    mode,
                );
                metadata.shmtable.insert(shmid, segment);
            }
        };
        shmid // return the shmid
    }

    //------------------SHMAT SYSCALL------------------

    pub fn shmat_syscall(&self, shmid: i32, shmaddr: *mut u8, shmflg: i32) -> i32 {
        let metadata = &SHM_METADATA;
        let prot: i32;
        if let Some(mut segment) = metadata.shmtable.get_mut(&shmid) {
            if 0 != (shmflg & fs_constants::SHM_RDONLY) {
                prot = PROT_READ;
            } else {
                prot = PROT_READ | PROT_WRITE;
            }
            let mut rev_shm = self.rev_shm.lock();
            rev_shm.push((shmaddr as u32, shmid));
            drop(rev_shm);

            // update semaphores
            if !segment.semaphor_offsets.is_empty() {
                // lets just look at the first cage in the set, since we only need to grab the ref from one
                if let Some(cageid) = segment
                    .attached_cages
                    .clone()
                    .into_read_only()
                    .keys()
                    .next()
                {
                    let cage2 = interface::cagetable_getref(*cageid);
                    let cage2_rev_shm = cage2.rev_shm.lock();
                    let addrs = Self::rev_shm_find_addrs_by_shmid(&cage2_rev_shm, shmid); // find all the addresses assoc. with shmid
                    for offset in segment.semaphor_offsets.iter() {
                        let sementry = cage2.sem_table.get(&(addrs[0] + *offset)).unwrap().clone(); //add  semaphors into semtable at addr + offsets
                        self.sem_table.insert(shmaddr as u32 + *offset, sementry);
                    }
                }
            }

            segment.map_shm(shmaddr, prot, self.cageid)
        } else {
            syscall_error(Errno::EINVAL, "shmat", "Invalid shmid value")
        }
    }

    //------------------SHMDT SYSCALL------------------

    pub fn shmdt_syscall(&self, shmaddr: *mut u8) -> i32 {
        let metadata = &SHM_METADATA;
        let mut rm = false;
        let mut rev_shm = self.rev_shm.lock();
        let rev_shm_index = Self::rev_shm_find_index_by_addr(&rev_shm, shmaddr as u32);

        if let Some(index) = rev_shm_index {
            let shmid = rev_shm[index].1;
            match metadata.shmtable.entry(shmid) {
                interface::RustHashEntry::Occupied(mut occupied) => {
                    let segment = occupied.get_mut();

                    // update semaphores
                    for offset in segment.semaphor_offsets.iter() {
                        self.sem_table.remove(&(shmaddr as u32 + *offset));
                    }

                    segment.unmap_shm(shmaddr, self.cageid);

                    if segment.rmid && segment.shminfo.shm_nattch == 0 {
                        rm = true;
                    }
                    rev_shm.swap_remove(index);

                    if rm {
                        let key = segment.key;
                        occupied.remove_entry();
                        metadata.shmkeyidtable.remove(&key);
                    }

                    return shmid; //NaCl relies on this non-posix behavior of returning the shmid on success
                }
                interface::RustHashEntry::Vacant(_) => {
                    panic!("Inode not created for some reason");
                }
            };
        } else {
            return syscall_error(
                Errno::EINVAL,
                "shmdt",
                "No shared memory segment at shmaddr",
            );
        }
    }

    //------------------SHMCTL SYSCALL------------------

    pub fn shmctl_syscall(&self, shmid: i32, cmd: i32, buf: Option<&mut ShmidsStruct>) -> i32 {
        let metadata = &SHM_METADATA;

        if let Some(mut segment) = metadata.shmtable.get_mut(&shmid) {
            match cmd {
                IPC_STAT => {
                    *buf.unwrap() = segment.shminfo;
                }
                IPC_RMID => {
                    segment.rmid = true;
                    segment.shminfo.shm_perm.mode |= SHM_DEST as u16;
                    if segment.shminfo.shm_nattch == 0 {
                        let key = segment.key;
                        drop(segment);
                        metadata.shmtable.remove(&shmid);
                        metadata.shmkeyidtable.remove(&key);
                    }
                }
                _ => {
                    return syscall_error(
                        Errno::EINVAL,
                        "shmctl",
                        "Arguments provided do not match implemented parameters",
                    );
                }
            }
        } else {
            return syscall_error(Errno::EINVAL, "shmctl", "Invalid identifier");
        }

        0 //shmctl has succeeded!
    }

    //------------------MUTEX SYSCALLS------------------
    pub fn mutex_create_syscall(&self) -> i32 {
        let mut mutextable = self.mutex_table.write();
        let mut index_option = None;
        for i in 0..mutextable.len() {
            if mutextable[i].is_none() {
                index_option = Some(i);
                break;
            }
        }

        let index = if let Some(ind) = index_option {
            ind
        } else {
            mutextable.push(None);
            mutextable.len() - 1
        };

        let mutex_result = interface::RawMutex::create();
        match mutex_result {
            Ok(mutex) => {
                mutextable[index] = Some(interface::RustRfc::new(mutex));
                index as i32
            }
            Err(_) => match Errno::from_discriminant(interface::get_errno()) {
                Ok(i) => syscall_error(
                    i,
                    "mutex_create",
                    "The libc call to pthread_mutex_init failed!",
                ),
                Err(()) => panic!("Unknown errno value from pthread_mutex_init returned!"),
            },
        }
    }

    pub fn mutex_destroy_syscall(&self, mutex_handle: i32) -> i32 {
        let mut mutextable = self.mutex_table.write();
        if mutex_handle < mutextable.len() as i32
            && mutex_handle >= 0
            && mutextable[mutex_handle as usize].is_some()
        {
            mutextable[mutex_handle as usize] = None;
            0
        } else {
            //undefined behavior
            syscall_error(
                Errno::EBADF,
                "mutex_destroy",
                "Mutex handle does not refer to a valid mutex!",
            )
        }
        //the RawMutex is destroyed on Drop

        //this is currently assumed to always succeed, as the man page does not list possible
        //errors for pthread_mutex_destroy
    }

    pub fn mutex_lock_syscall(&self, mutex_handle: i32) -> i32 {
        let mutextable = self.mutex_table.read();
        if mutex_handle < mutextable.len() as i32
            && mutex_handle >= 0
            && mutextable[mutex_handle as usize].is_some()
        {
            let clonedmutex = mutextable[mutex_handle as usize].as_ref().unwrap().clone();
            drop(mutextable);
            let retval = clonedmutex.lock();

            if retval < 0 {
                match Errno::from_discriminant(interface::get_errno()) {
                    Ok(i) => {
                        return syscall_error(
                            i,
                            "mutex_lock",
                            "The libc call to pthread_mutex_lock failed!",
                        );
                    }
                    Err(()) => panic!("Unknown errno value from pthread_mutex_lock returned!"),
                };
            }

            retval
        } else {
            //undefined behavior
            syscall_error(
                Errno::EBADF,
                "mutex_lock",
                "Mutex handle does not refer to a valid mutex!",
            )
        }
    }

    pub fn mutex_trylock_syscall(&self, mutex_handle: i32) -> i32 {
        let mutextable = self.mutex_table.read();
        if mutex_handle < mutextable.len() as i32
            && mutex_handle >= 0
            && mutextable[mutex_handle as usize].is_some()
        {
            let clonedmutex = mutextable[mutex_handle as usize].as_ref().unwrap().clone();
            drop(mutextable);
            let retval = clonedmutex.trylock();

            if retval < 0 {
                match Errno::from_discriminant(interface::get_errno()) {
                    Ok(i) => {
                        return syscall_error(
                            i,
                            "mutex_trylock",
                            "The libc call to pthread_mutex_trylock failed!",
                        );
                    }
                    Err(()) => panic!("Unknown errno value from pthread_mutex_trylock returned!"),
                };
            }

            retval
        } else {
            //undefined behavior
            syscall_error(
                Errno::EBADF,
                "mutex_trylock",
                "Mutex handle does not refer to a valid mutex!",
            )
        }
    }

    pub fn mutex_unlock_syscall(&self, mutex_handle: i32) -> i32 {
        let mutextable = self.mutex_table.read();
        if mutex_handle < mutextable.len() as i32
            && mutex_handle >= 0
            && mutextable[mutex_handle as usize].is_some()
        {
            let clonedmutex = mutextable[mutex_handle as usize].as_ref().unwrap().clone();
            drop(mutextable);
            let retval = clonedmutex.unlock();

            if retval < 0 {
                match Errno::from_discriminant(interface::get_errno()) {
                    Ok(i) => {
                        return syscall_error(
                            i,
                            "mutex_unlock",
                            "The libc call to pthread_mutex_unlock failed!",
                        );
                    }
                    Err(()) => panic!("Unknown errno value from pthread_mutex_unlock returned!"),
                };
            }

            retval
        } else {
            //undefined behavior
            syscall_error(
                Errno::EBADF,
                "mutex_unlock",
                "Mutex handle does not refer to a valid mutex!",
            )
        }
    }

    //------------------CONDVAR SYSCALLS------------------

    pub fn cond_create_syscall(&self) -> i32 {
        let mut cvtable = self.cv_table.write();
        let mut index_option = None;
        for i in 0..cvtable.len() {
            if cvtable[i].is_none() {
                index_option = Some(i);
                break;
            }
        }

        let index = if let Some(ind) = index_option {
            ind
        } else {
            cvtable.push(None);
            cvtable.len() - 1
        };

        let cv_result = interface::RawCondvar::create();
        match cv_result {
            Ok(cv) => {
                cvtable[index] = Some(interface::RustRfc::new(cv));
                index as i32
            }
            Err(_) => match Errno::from_discriminant(interface::get_errno()) {
                Ok(i) => syscall_error(
                    i,
                    "cond_create",
                    "The libc call to pthread_cond_init failed!",
                ),
                Err(()) => panic!("Unknown errno value from pthread_cond_init returned!"),
            },
        }
    }

    pub fn cond_destroy_syscall(&self, cv_handle: i32) -> i32 {
        let mut cvtable = self.cv_table.write();
        if cv_handle < cvtable.len() as i32
            && cv_handle >= 0
            && cvtable[cv_handle as usize].is_some()
        {
            cvtable[cv_handle as usize] = None;
            0
        } else {
            //undefined behavior
            syscall_error(
                Errno::EBADF,
                "cond_destroy",
                "Condvar handle does not refer to a valid condvar!",
            )
        }
        //the RawCondvar is destroyed on Drop

        //this is currently assumed to always succeed, as the man page does not list possible
        //errors for pthread_cv_destroy
    }

    pub fn cond_signal_syscall(&self, cv_handle: i32) -> i32 {
        let cvtable = self.cv_table.read();
        if cv_handle < cvtable.len() as i32
            && cv_handle >= 0
            && cvtable[cv_handle as usize].is_some()
        {
            let clonedcv = cvtable[cv_handle as usize].as_ref().unwrap().clone();
            drop(cvtable);
            let retval = clonedcv.signal();

            if retval < 0 {
                match Errno::from_discriminant(interface::get_errno()) {
                    Ok(i) => {
                        return syscall_error(
                            i,
                            "cond_signal",
                            "The libc call to pthread_cond_signal failed!",
                        );
                    }
                    Err(()) => panic!("Unknown errno value from pthread_cond_signal returned!"),
                };
            }

            retval
        } else {
            //undefined behavior
            syscall_error(
                Errno::EBADF,
                "cond_signal",
                "Condvar handle does not refer to a valid condvar!",
            )
        }
    }

    pub fn cond_broadcast_syscall(&self, cv_handle: i32) -> i32 {
        let cvtable = self.cv_table.read();
        if cv_handle < cvtable.len() as i32
            && cv_handle >= 0
            && cvtable[cv_handle as usize].is_some()
        {
            let clonedcv = cvtable[cv_handle as usize].as_ref().unwrap().clone();
            drop(cvtable);
            let retval = clonedcv.broadcast();

            if retval < 0 {
                match Errno::from_discriminant(interface::get_errno()) {
                    Ok(i) => {
                        return syscall_error(
                            i,
                            "cond_broadcast",
                            "The libc call to pthread_cond_broadcast failed!",
                        );
                    }
                    Err(()) => panic!("Unknown errno value from pthread_cond_broadcast returned!"),
                };
            }

            retval
        } else {
            //undefined behavior
            syscall_error(
                Errno::EBADF,
                "cond_broadcast",
                "Condvar handle does not refer to a valid condvar!",
            )
        }
    }

    pub fn cond_wait_syscall(&self, cv_handle: i32, mutex_handle: i32) -> i32 {
        let cvtable = self.cv_table.read();
        if cv_handle < cvtable.len() as i32
            && cv_handle >= 0
            && cvtable[cv_handle as usize].is_some()
        {
            let clonedcv = cvtable[cv_handle as usize].as_ref().unwrap().clone();
            drop(cvtable);

            let mutextable = self.mutex_table.read();
            if mutex_handle < mutextable.len() as i32
                && mutex_handle >= 0
                && mutextable[mutex_handle as usize].is_some()
            {
                let clonedmutex = mutextable[mutex_handle as usize].as_ref().unwrap().clone();
                drop(mutextable);
                let retval = clonedcv.wait(&*clonedmutex);

                // if the cancel status is set in the cage, we trap around a cancel point
                // until the individual thread is signaled to cancel itself
                if self
                    .cancelstatus
                    .load(interface::RustAtomicOrdering::Relaxed)
                {
                    loop {
                        interface::cancelpoint(self.cageid);
                    } // we check cancellation status here without letting the function return
                }

                if retval < 0 {
                    match Errno::from_discriminant(interface::get_errno()) {
                        Ok(i) => {
                            return syscall_error(
                                i,
                                "cond_wait",
                                "The libc call to pthread_cond_wait failed!",
                            );
                        }
                        Err(()) => panic!("Unknown errno value from pthread_cond_wait returned!"),
                    };
                }

                retval
            } else {
                //undefined behavior
                syscall_error(
                    Errno::EBADF,
                    "cond_wait",
                    "Mutex handle does not refer to a valid mutex!",
                )
            }
        } else {
            //undefined behavior
            syscall_error(
                Errno::EBADF,
                "cond_wait",
                "Condvar handle does not refer to a valid condvar!",
            )
        }
    }

    pub fn cond_timedwait_syscall(
        &self,
        cv_handle: i32,
        mutex_handle: i32,
        time: interface::RustDuration,
    ) -> i32 {
        let cvtable = self.cv_table.read();
        if cv_handle < cvtable.len() as i32
            && cv_handle >= 0
            && cvtable[cv_handle as usize].is_some()
        {
            let clonedcv = cvtable[cv_handle as usize].as_ref().unwrap().clone();
            drop(cvtable);

            let mutextable = self.mutex_table.read();
            if mutex_handle < mutextable.len() as i32
                && mutex_handle >= 0
                && mutextable[mutex_handle as usize].is_some()
            {
                let clonedmutex = mutextable[mutex_handle as usize].as_ref().unwrap().clone();
                drop(mutextable);
                let retval = clonedcv.timedwait(&*clonedmutex, time);
                if retval < 0 {
                    match Errno::from_discriminant(interface::get_errno()) {
                        Ok(i) => {
                            return syscall_error(
                                i,
                                "cond_wait",
                                "The libc call to pthread_cond_wait failed!",
                            );
                        }
                        Err(()) => panic!("Unknown errno value from pthread_cond_wait returned!"),
                    };
                }

                retval
            } else {
                //undefined behavior
                syscall_error(
                    Errno::EBADF,
                    "cond_wait",
                    "Mutex handle does not refer to a valid mutex!",
                )
            }
        } else {
            //undefined behavior
            syscall_error(
                Errno::EBADF,
                "cond_wait",
                "Condvar handle does not refer to a valid condvar!",
            )
        }
    }

    //------------------SEMAPHORE SYSCALLS------------------
    /*
     *  Initialize semaphore object SEM to value
     *  pshared used to indicate whether the semaphore is shared in threads (when equals to 0)
     *  or shared between processes (when nonzero)
     */
    pub fn sem_init_syscall(&self, sem_handle: u32, pshared: i32, value: u32) -> i32 {
        // Boundary check
        if value > SEM_VALUE_MAX {
            return syscall_error(Errno::EINVAL, "sem_init", "value exceeds SEM_VALUE_MAX");
        }

        let metadata = &SHM_METADATA;
        let is_shared = pshared != 0;

        // Iterate semaphore table, if semaphore is already initialzed return error
        let semtable = &self.sem_table;

        // Will initialize only it's new
        if !semtable.contains_key(&sem_handle) {
            let new_semaphore =
                interface::RustRfc::new(interface::RustSemaphore::new(value, is_shared));
            semtable.insert(sem_handle, new_semaphore.clone());

            if is_shared {
                let rev_shm = self.rev_shm.lock();
                // if its shared and exists in an existing mapping we need to add it to other cages
                if let Some((mapaddr, shmid)) =
                    Self::search_for_addr_in_region(&rev_shm, sem_handle)
                {
                    let offset = mapaddr - sem_handle;
                    if let Some(segment) = metadata.shmtable.get_mut(&shmid) {
                        for cageid in segment.attached_cages.clone().into_read_only().keys() {
                            // iterate through all cages with segment attached and add semaphor in segments at attached addr + offset
                            let cage = interface::cagetable_getref(*cageid);
                            let addrs = Self::rev_shm_find_addrs_by_shmid(&rev_shm, shmid);
                            for addr in addrs.iter() {
                                cage.sem_table.insert(addr + offset, new_semaphore.clone());
                            }
                        }
                        segment.semaphor_offsets.insert(offset);
                    }
                }
            }
            return 0;
        }

        return syscall_error(Errno::EBADF, "sem_init", "semaphore already initialized");
    }

    pub fn sem_wait_syscall(&self, sem_handle: u32) -> i32 {
        let semtable = &self.sem_table;
        // Check whether semaphore exists
        if let Some(sementry) = semtable.get_mut(&sem_handle) {
            let semaphore = sementry.clone();
            drop(sementry);
            semaphore.lock();
        } else {
            return syscall_error(Errno::EINVAL, "sem_wait", "sem is not a valid semaphore");
        }
        return 0;
    }

    pub fn sem_post_syscall(&self, sem_handle: u32) -> i32 {
        let semtable = &self.sem_table;
        if let Some(sementry) = semtable.get_mut(&sem_handle) {
            let semaphore = sementry.clone();
            drop(sementry);
            if !semaphore.unlock() {
                return syscall_error(
                    Errno::EOVERFLOW,
                    "sem_post",
                    "The maximum allowable value for a semaphore would be exceeded",
                );
            }
        } else {
            return syscall_error(Errno::EINVAL, "sem_wait", "sem is not a valid semaphore");
        }
        return 0;
    }

    pub fn sem_destroy_syscall(&self, sem_handle: u32) -> i32 {
        let metadata = &SHM_METADATA;

        let semtable = &self.sem_table;
        // remove entry from semaphore table
        if let Some(sementry) = semtable.remove(&sem_handle) {
            if sementry
                .1
                .is_shared
                .load(interface::RustAtomicOrdering::Relaxed)
            {
                // if its shared we'll need to remove it from other attachments
                let rev_shm = self.rev_shm.lock();
                if let Some((mapaddr, shmid)) =
                    Self::search_for_addr_in_region(&rev_shm, sem_handle)
                {
                    // find all segments that contain semaphore
                    let offset = mapaddr - sem_handle;
                    if let Some(segment) = metadata.shmtable.get_mut(&shmid) {
                        for cageid in segment.attached_cages.clone().into_read_only().keys() {
                            // iterate through all cages containing segment
                            let cage = interface::cagetable_getref(*cageid);
                            let addrs = Self::rev_shm_find_addrs_by_shmid(&rev_shm, shmid);
                            for addr in addrs.iter() {
                                cage.sem_table.remove(&(addr + offset)); //remove semapoores at attached addresses + the offset
                            }
                        }
                    }
                }
            }
            return 0;
        } else {
            return syscall_error(Errno::EINVAL, "sem_destroy", "sem is not a valid semaphore");
        }
    }

    /*
     * Take only sem_t *sem as argument, and return int *sval
     */
    pub fn sem_getvalue_syscall(&self, sem_handle: u32) -> i32 {
        let semtable = &self.sem_table;
        if let Some(sementry) = semtable.get_mut(&sem_handle) {
            let semaphore = sementry.clone();
            drop(sementry);
            return semaphore.get_value();
        }
        return syscall_error(
            Errno::EINVAL,
            "sem_getvalue",
            "sem is not a valid semaphore",
        );
    }

    pub fn sem_trywait_syscall(&self, sem_handle: u32) -> i32 {
        let semtable = &self.sem_table;
        // Check whether semaphore exists
        if let Some(sementry) = semtable.get_mut(&sem_handle) {
            let semaphore = sementry.clone();
            drop(sementry);
            if !semaphore.trylock() {
                return syscall_error(
                    Errno::EAGAIN,
                    "sem_trywait",
                    "The operation could not be performed without blocking",
                );
            }
        } else {
            return syscall_error(Errno::EINVAL, "sem_trywait", "sem is not a valid semaphore");
        }
        return 0;
    }

    pub fn sem_timedwait_syscall(&self, sem_handle: u32, time: interface::RustDuration) -> i32 {
        let abstime = libc::timespec {
            tv_sec: time.as_secs() as i64,
            tv_nsec: (time.as_nanos() % 1000000000) as i64,
        };
        if abstime.tv_nsec < 0 {
            return syscall_error(Errno::EINVAL, "sem_timedwait", "Invalid timedout");
        }
        let semtable = &self.sem_table;
        // Check whether semaphore exists
        if let Some(sementry) = semtable.get_mut(&sem_handle) {
            let semaphore = sementry.clone();
            drop(sementry);
            if !semaphore.timedlock(time) {
                return syscall_error(
                    Errno::ETIMEDOUT,
                    "sem_timedwait",
                    "The call timed out before the semaphore could be locked",
                );
            }
        } else {
            return syscall_error(
                Errno::EINVAL,
                "sem_timedwait",
                "sem is not a valid semaphore",
            );
        }
        return 0;
    }
}

pub fn kernel_close(kernelfd: u64) {
    let ret = unsafe {
        libc::close(kernelfd as i32)
    };
    if ret != 0 {
        let err = unsafe {
            libc::__errno_location()
        };
        let err_str = unsafe {
            libc::strerror(*err)
        };
        let err_msg = unsafe {
            CStr::from_ptr(err_str).to_string_lossy().into_owned()
        };
        println!("errno: {:?}", err);
        println!("Error message: {:?}", err_msg);
        io::stdout().flush().unwrap();
        panic!("kernel close failed! ");
    }
}