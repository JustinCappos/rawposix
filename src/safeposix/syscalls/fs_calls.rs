#![allow(dead_code)]

// File system related system calls
use super::fs_constants::*;
use super::sys_constants::*;
use crate::interface;
use crate::safeposix::cage::Errno::EINVAL;
use crate::safeposix::cage::{FileDescriptor::*, *};
use crate::safeposix::filesystem::*;
use crate::safeposix::net::NET_METADATA;
use crate::safeposix::shm::*;

use libc::*;

/* 
*   We will receive parameters with type u64 by default, then we will do type conversion inside
*   of each syscall
*   
*   [Concerns]
*   - cloexec in get_unused_virtual_fd()..?
*   - there's no getdents() API in rust libc
*   
*   [TODO]
*   - close() for imp
*   - fcntl() for different return type (including the imp)
*   - pipe() / pipe2()
*/

impl Cage {
    //------------------------------------OPEN SYSCALL------------------------------------
    /* 
    *   Open will return a file descriptor 
    *   Mapping a new virtual fd and kernel fd that libc::socket returned
    *   Then return virtual fd
    */
    pub fn open_syscall(&self, path: &str, oflag: u64, mode: u64) -> i32 {
        // Convert data type from &str into *const i8
        let (path_c, _, _) = path.to_string().into_raw_parts();

        let kernel_fd = unsafe { libc::open(path_c as *const i8, oflag as i32) };

        let virtual_fd = get_unused_virtual_fd(self.cageid, kernel_fd, false, 0).unwrap();
        virtual_fd
    }

    //------------------MKDIR SYSCALL------------------
    /*
    *   mkdir() will return 0 when success and -1 when fail 
    */
    pub fn mkdir_syscall(&self, path: &str, mode: u64) -> i32 {
        // Convert data type from &str into *const i8
        let (path_c, _, _) = path.to_string().into_raw_parts();
        unsafe {
            libc::mkdir(path_c as *const i8, mode as u16)
        }
    }

    //------------------MKNOD SYSCALL------------------
    /*
    *   mknod() will return 0 when success and -1 when fail 
    */
    pub fn mknod_syscall(&self, path: &str, mode: u64, dev: u64) -> i32 {
        // Convert data type from &str into *const i8
        let (path_c, _, _) = path.to_string().into_raw_parts();
        unsafe {
            libc::mknod(path_c as *const i8, mode as u16, dev as i32)
        }
    }

    //------------------------------------LINK SYSCALL------------------------------------
    /*
    *   link() will return 0 when success and -1 when fail 
    */
    pub fn link_syscall(&self, oldpath: &str, newpath: &str) -> i32 {
        // Convert data type from &str into *const i8
        let (oldpath_c, _, _) = oldpath.to_string().into_raw_parts();
        let (newpath_c, _, _) = newpath.to_string().into_raw_parts();
        unsafe {
            libc::link(oldpath_c as *const i8, newpath_c as *const i8)
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
    pub fn creat_syscall(&self, path: &str, mode: u64) -> i32 {
        let (path_c, _, _) = path.to_string().into_raw_parts();
        let kernel_fd = unsafe {
            libc::creat(path_c as *const i8, mode as u16)
        };
        let virtual_fd = get_unused_virtual_fd(self.cageid, kernel_fd, false, 0).unwrap();
        virtual_fd
    }

    //------------------------------------STAT SYSCALL------------------------------------
    /*
    *   stat() will return 0 when success and -1 when fail 
    */
    pub fn stat_syscall(&self, path: &str, statbuf: &mut stat) -> i32 {
        let (path_c, _, _) = path.to_string().into_raw_parts();
        unsafe {
            libc::stat(path_c as *const i8, statbuf)
        }
    }

    //------------------------------------FSTAT SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   fstat() will return 0 when success and -1 when fail 
    */
    pub fn fstat_syscall(&self, virtual_fd: u64, statbuf: &mut stat) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe {
            libc::fstat(kernel_fd, statbuf)
        }
    }

    //------------------------------------STATFS SYSCALL------------------------------------
    /*
    *   statfs() will return 0 when success and -1 when fail 
    */
    pub fn statfs_syscall(&self, path: &str, databuf: &mut statfs) -> i32 {
        let (path_c, _, _) = path.to_string().into_raw_parts();
        unsafe {
            libc::statfs(path_c as *const i8, databuf)
        }
    }

    //------------------------------------FSTATFS SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   fstatfs() will return 0 when success and -1 when fail 
    */
    pub fn fstatfs_syscall(&self, virtual_fd: u64, databuf: &mut statfs) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe{
            libc::fstatfs(kernel_fd, databuf)
        }
    }

    //------------------------------------READ SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   read() will return:
    *   - the number of bytes read is returned, success
    *   - -1, fail 
    */
    pub fn read_syscall(&self, virtual_fd: u64, readbuf: *mut u8, count: u64) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe {
            libc::read(kernel_fd, readbuf as *mut c_void, count as usize) as i32
        }
    }

    //------------------------------------PREAD SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   pread() will return:
    *   - the number of bytes read is returned, success
    *   - -1, fail 
    */
    pub fn pread_syscall(&self, virtual_fd: u64, buf: *mut u8, count: u64, offset: u64) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe {
            libc::pread(kernel_fd, buf as *mut c_void, count as usize, offset as i64) as i32
        }
    }

    //------------------------------------WRITE SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   write() will return:
    *   - the number of bytes writen is returned, success
    *   - -1, fail 
    */
    pub fn write_syscall(&self, virtual_fd: u64, buf: *const u8, count: u64) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe {
            libc::write(kernel_fd, buf as *const c_void, count as usize) as i32
        }
    }

    //------------------------------------PWRITE SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   pwrite() will return:
    *   - the number of bytes read is returned, success
    *   - -1, fail 
    */
    pub fn pwrite_syscall(&self, virtual_fd: u64, buf: *const u8, count: u64, offset: u64) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe {
            libc::pwrite(kernel_fd, buf as *const c_void, count as usize, offset as i64) as i32
        }
    }

    //------------------------------------LSEEK SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   lseek() will return:
    *   -  the resulting offset location as measured in bytes from the beginning of the file
    *   - -1, fail 
    */
    pub fn lseek_syscall(&self, virtual_fd: u64, offset: u64, whence: u64) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe {
            libc::lseek(kernel_fd, offset as i64, whence as i32) as i32
        }
    }

    //------------------------------------ACCESS SYSCALL------------------------------------
    /*
    *   access() will return 0 when sucess, -1 when fail 
    */
    pub fn access_syscall(&self, path: &str, amode: u64) -> i32 {
        let (path_c, _, _) = path.to_string().into_raw_parts();
        unsafe {
            libc::access(path_c as *const i8, amode as i32)
        }
    }

    //------------------------------------FCHDIR SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   fchdir() will return 0 when sucess, -1 when fail 
    */
    pub fn fchdir_syscall(&self, virtual_fd: u64) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe {
            libc::fchdir(kernel_fd)
        }
    }

    //------------------------------------CHDIR SYSCALL------------------------------------
    /*
    *   chdir() will return 0 when sucess, -1 when fail 
    */
    pub fn chdir_syscall(&self, path: &str) -> i32 {
        let (path_c, _, _) = path.to_string().into_raw_parts();
        unsafe {
            libc::chdir(path_c as *const i8)
        }
    }

    //------------------------------------DUP & DUP2 SYSCALLS------------------------------------

    pub fn dup_syscall(&self, fd: i32, start_desc: Option<i32>) -> i32 {
        //if a starting fd was passed, then use that as the starting point, but otherwise, use the designated minimum of STARTINGFD
        let start_fd = match start_desc {
            Some(start_desc) => start_desc,
            None => STARTINGFD,
        };

        if start_fd == fd {
            return start_fd;
        } //if the file descriptors are equal, return the new one

        // get the filedesc_enum
        let checkedfd = self.get_filedescriptor(fd).unwrap();
        let filedesc_enum = checkedfd.write();
        let filedesc_enum = if let Some(f) = &*filedesc_enum {
            f
        } else {
            return syscall_error(Errno::EBADF, "dup", "Invalid old file descriptor.");
        };

        //checking whether the fd exists in the file table
        return Self::_dup2_helper(&self, filedesc_enum, start_fd, false);
    }

    pub fn dup2_syscall(&self, oldfd: i32, newfd: i32) -> i32 {
        //checking if the new fd is out of range
        if newfd >= MAXFD || newfd < 0 {
            return syscall_error(
                Errno::EBADF,
                "dup2",
                "provided file descriptor is out of range",
            );
        }

        if newfd == oldfd {
            return newfd;
        } //if the file descriptors are equal, return the new one

        // get the filedesc_enum
        let checkedfd = self.get_filedescriptor(oldfd).unwrap();
        let filedesc_enum = checkedfd.write();
        let filedesc_enum = if let Some(f) = &*filedesc_enum {
            f
        } else {
            return syscall_error(Errno::EBADF, "dup2", "Invalid old file descriptor.");
        };

        //if the old fd exists, execute the helper, else return error
        return Self::_dup2_helper(&self, filedesc_enum, newfd, true);
    }

    pub fn _dup2_helper(&self, filedesc_enum: &FileDescriptor, newfd: i32, fromdup2: bool) -> i32 {
        let (dupfd, mut dupfdguard) = if fromdup2 {
            let mut fdguard = self.filedescriptortable[newfd as usize].write();
            let closebool = fdguard.is_some();
            drop(fdguard);
            // close the fd in the way of the new fd. mirror the implementation of linux, ignore the potential error of the close here
            if closebool {
                let _close_result = Self::_close_helper_inner(&self, newfd);
            }

            // re-grab clean fd
            fdguard = self.filedescriptortable[newfd as usize].write();
            (newfd, fdguard)
        } else {
            let (newdupfd, guardopt) = self.get_next_fd(Some(newfd));
            if newdupfd < 0 {
                return syscall_error(
                    Errno::ENFILE,
                    "dup2_helper",
                    "no available file descriptor number could be found",
                );
            }
            (newdupfd, guardopt.unwrap())
        };

        let dupfdoption = &mut *dupfdguard;

        match filedesc_enum {
            File(normalfile_filedesc_obj) => {
                let inodenum = normalfile_filedesc_obj.inode;
                let mut inodeobj = FS_METADATA.inodetable.get_mut(&inodenum).unwrap();
                //incrementing the ref count so that when close is executed on the dup'd file
                //the original file does not get a negative ref count
                match *inodeobj {
                    Inode::File(ref mut normalfile_inode_obj) => {
                        normalfile_inode_obj.refcount += 1;
                    }
                    Inode::Dir(ref mut dir_inode_obj) => {
                        dir_inode_obj.refcount += 1;
                    }
                    Inode::CharDev(ref mut chardev_inode_obj) => {
                        chardev_inode_obj.refcount += 1;
                    }
                    Inode::Socket(_) => panic!("dup: fd and inode do not match."),
                }
            }
            Pipe(pipe_filedesc_obj) => {
                pipe_filedesc_obj.pipe.incr_ref(pipe_filedesc_obj.flags);
            }
            Socket(ref socket_filedesc_obj) => {
                //we handle the closing of sockets on drop
                // checking whether this is a domain socket

                let sock_tmp = socket_filedesc_obj.handle.clone();
                let sockhandle = sock_tmp.write();
                let socket_type = sockhandle.domain;
                if socket_type == AF_UNIX {
                    if let Some(sockinfo) = &sockhandle.unix_info {
                        if let Some(sendpipe) = sockinfo.sendpipe.as_ref() {
                            sendpipe.incr_ref(O_WRONLY);
                        }
                        if let Some(receivepipe) = sockinfo.receivepipe.as_ref() {
                            receivepipe.incr_ref(O_RDONLY);
                        }
                    }
                }
            }
            Stream(_normalfile_filedesc_obj) => {
                // no stream refs
            }
            _ => {
                return syscall_error(Errno::EACCES, "dup or dup2", "can't dup the provided file");
            }
        }

        let mut dupd_fd_enum = filedesc_enum.clone(); //clones the arc for sockethandle

        // get and clone fd, wrap and insert into table.
        match dupd_fd_enum {
            // we don't want to pass on the CLOEXEC flag
            File(ref mut normalfile_filedesc_obj) => {
                normalfile_filedesc_obj.flags = normalfile_filedesc_obj.flags & !O_CLOEXEC;
            }
            Pipe(ref mut pipe_filedesc_obj) => {
                pipe_filedesc_obj.flags = pipe_filedesc_obj.flags & !O_CLOEXEC;
            }
            Socket(ref mut socket_filedesc_obj) => {
                // can do this for domainsockets and sockets
                socket_filedesc_obj.flags = socket_filedesc_obj.flags & !O_CLOEXEC;
            }
            Stream(ref mut stream_filedesc_obj) => {
                stream_filedesc_obj.flags = stream_filedesc_obj.flags & !O_CLOEXEC;
            }
            _ => {
                return syscall_error(Errno::EACCES, "dup or dup2", "can't dup the provided file");
            }
        }

        let _insertval = dupfdoption.insert(dupd_fd_enum);

        return dupfd;
    }

    //------------------------------------CLOSE SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   close() will return 0 when sucess, -1 when fail 
    */
    pub fn close_syscall(&self, virtual_fd: u64) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe {
            libc::close(kernel_fd)
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
    pub fn fcntl_syscall(&self, fd: i32, cmd: i32, arg: i32) -> i32 {
        let checkedfd = self.get_filedescriptor(fd).unwrap();
        let mut unlocked_fd = checkedfd.write();
        if let Some(filedesc_enum) = &mut *unlocked_fd {
            let flags = match filedesc_enum {
                Epoll(obj) => &mut obj.flags,
                Pipe(obj) => &mut obj.flags,
                Stream(obj) => &mut obj.flags,
                File(obj) => &mut obj.flags,
                Socket(ref mut sockfdobj) => {
                    if cmd == F_SETFL && arg >= 0 {
                        let sock_tmp = sockfdobj.handle.clone();
                        let mut sockhandle = sock_tmp.write();

                        if let Some(ins) = &mut sockhandle.innersocket {
                            let fcntlret;
                            if arg & O_NONBLOCK == O_NONBLOCK {
                                //set for non-blocking I/O
                                fcntlret = ins.set_nonblocking();
                            } else {
                                //clear non-blocking I/O
                                fcntlret = ins.set_blocking();
                            }
                            if fcntlret < 0 {
                                match Errno::from_discriminant(interface::get_errno()) {
                                    Ok(i) => {
                                        return syscall_error(
                                            i,
                                            "fcntl",
                                            "The libc call to fcntl failed!",
                                        );
                                    }
                                    Err(()) => panic!("Unknown errno value from fcntl returned!"),
                                };
                            }
                        }
                    }

                    &mut sockfdobj.flags
                }
            };

            //matching the tuple
            match (cmd, arg) {
                //because the arg parameter is not used in certain commands, it can be anything (..)
                (F_GETFD, ..) => *flags & O_CLOEXEC,
                // set the flags but make sure that the flags are valid
                (F_SETFD, arg) if arg >= 0 => {
                    if arg & O_CLOEXEC != 0 {
                        *flags |= O_CLOEXEC;
                    } else {
                        *flags &= !O_CLOEXEC;
                    }
                    0
                }
                (F_GETFL, ..) => {
                    //for get, we just need to return the flags
                    *flags & !O_CLOEXEC
                }
                (F_SETFL, arg) if arg >= 0 => {
                    *flags |= arg;
                    0
                }
                (F_DUPFD, arg) if arg >= 0 => self._dup2_helper(&filedesc_enum, arg, false),
                //TO DO: implement. this one is saying get the signals
                (F_GETOWN, ..) => {
                    0 //TO DO: traditional SIGIO behavior
                }
                (F_SETOWN, arg) if arg >= 0 => {
                    0 //this would return the PID if positive and the process group if negative,
                      //either way do nothing and return success
                }
                _ => syscall_error(
                    Errno::EINVAL,
                    "fcntl",
                    "Arguments provided do not match implemented parameters",
                ),
            }
        } else {
            syscall_error(Errno::EBADF, "fcntl", "Invalid file descriptor")
        }
    }

    //------------------------------------IOCTL SYSCALL------------------------------------

    pub fn ioctl_syscall(&self, fd: i32, request: u32, ptrunion: IoctlPtrUnion) -> i32 {
        let checkedfd = self.get_filedescriptor(fd).unwrap();
        let mut unlocked_fd = checkedfd.write();
        if let Some(filedesc_enum) = &mut *unlocked_fd {
            match request {
                FIONBIO => {
                    let arg_result = interface::get_ioctl_int(ptrunion);
                    //matching the tuple and passing in filedesc_enum
                    match (arg_result, filedesc_enum) {
                        (Err(arg_result), ..)=> {
                            return arg_result; //syscall_error
                        }
                        (Ok(arg_result), Socket(ref mut sockfdobj)) => {
                            let sock_tmp = sockfdobj.handle.clone();
                            let mut sockhandle = sock_tmp.write();

                            let flags = &mut sockfdobj.flags;
                            let arg: i32 = arg_result;
                            let mut ioctlret = 0;

                            if arg == 0 { //clear non-blocking I/O
                                *flags &= !O_NONBLOCK;
                                if let Some(ins) = &mut sockhandle.innersocket {
                                    ioctlret = ins.set_blocking();
                                }
                            } else { //set for non-blocking I/O
                                *flags |= O_NONBLOCK;
                                if let Some(ins) = &mut sockhandle.innersocket {
                                    ioctlret = ins.set_nonblocking();
                                }
                            }
                            if ioctlret < 0 {
                                match Errno::from_discriminant(interface::get_errno()) {
                                    Ok(i) => {return syscall_error(i, "ioctl", "The libc call to ioctl failed!");},
                                    Err(()) => panic!("Unknown errno value from ioctl returned!"),
                                };
                            }

                            0
                        }
                        _ => {syscall_error(Errno::ENOTTY, "ioctl", "The specified request does not apply to the kind of object that the file descriptor fd references.")}
                    }
                }
                FIOASYNC => {
                    //not implemented
                    interface::log_verbose(
                        "ioctl(FIOASYNC) is not implemented, and just returns 0.",
                    );
                    0
                }
                _ => syscall_error(
                    Errno::EINVAL,
                    "ioctl",
                    "Arguments provided do not match implemented parameters",
                ),
            }
        } else {
            syscall_error(Errno::EBADF, "ioctl", "Invalid file descriptor")
        }
    }


    //------------------------------------CHMOD SYSCALL------------------------------------
    /*
    *   chmod() will return 0 when success and -1 when fail 
    */
    pub fn chmod_syscall(&self, path: &str, mode: u64) -> i32 {
        let (path_c, _, _) = path.to_string().into_raw_parts();
        unsafe {
            libc::chmod(path_c as *const i8, mode as u16)
        }
    }

    //------------------------------------FCHMOD SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   fchmod() will return 0 when sucess, -1 when fail 
    */
    pub fn fchmod_syscall(&self, virtual_fd: u64, mode: u64) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe {
            libc::fchmod(kernel_fd, mode as u16)
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
        len: u64,
        prot: u64,
        flags: u64,
        virtual_fd: u64,
        off: u64,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        // Do type conversion to translate from c_void into i32
        unsafe {
            ((libc::mmap(addr as *mut c_void, len as usize, prot as i32, flags as i32, kernel_fd, off as i64) as i64) 
                & 0xffffffff) as i32
        }
    }

    //------------------------------------MUNMAP SYSCALL------------------------------------
    /*
    *   munmap() will return:
    *   - 0, success
    *   - -1, fail
    */
    pub fn munmap_syscall(&self, addr: *mut u8, len: u64) -> i32 {
        unsafe {
            libc::munmap(addr as *mut c_void, len as usize)
        }
    }

    //------------------------------------FLOCK SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   flock() will return 0 when sucess, -1 when fail 
    */
    pub fn flock_syscall(&self, virtual_fd: u64, operation: u64) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe {
            libc::flock(kernel_fd, operation as i32)
        }
    }

    //------------------RMDIR SYSCALL------------------
    /*
    *   rmdir() will return 0 when sucess, -1 when fail 
    */
    pub fn rmdir_syscall(&self, path: &str) -> i32 {
        let (path_c, _, _) = path.to_string().into_raw_parts();
        unsafe {
            libc::rmdir(path_c as *const i8)
        }
    }

    //------------------RENAME SYSCALL------------------
    /*
    *   rename() will return 0 when sucess, -1 when fail 
    */
    pub fn rename_syscall(&self, oldpath: &str, newpath: &str) -> i32 {
        let (oldpath_c, _, _) = oldpath.to_string().into_raw_parts();
        let (newpath_c, _, _) = newpath.to_string().into_raw_parts();
        unsafe {
            libc::rename(oldpath_c as *const i8, newpath_c as *const i8)
        }
    }

    //------------------------------------FSYNC SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   fsync() will return 0 when sucess, -1 when fail 
    */
    pub fn fsync_syscall(&self, virtual_fd: u64) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe {
            libc::fsync(kernel_fd)
        }
    }

    //------------------------------------FDATASYNC SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   fdatasync() will return 0 when sucess, -1 when fail 
    */
    pub fn fdatasync_syscall(&self, virtual_fd: u64) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe {
            libc::fdatasync(kernel_fd)
        }
    }

    //------------------------------------SYNC_FILE_RANGE SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   sync_file_range() will return 0 when sucess, -1 when fail 
    */
    pub fn sync_file_range_syscall(
        &self,
        virtual_fd: u64,
        offset: u64,
        nbytes: u64,
        flags: u64,
    ) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe {
            libc::sync_file_range(kernel_fd, offset as i64, nbytes as i64, flags as u32)
        }
    }

    //------------------FTRUNCATE SYSCALL------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   ftruncate() will return 0 when sucess, -1 when fail 
    */
    pub fn ftruncate_syscall(&self, virtual_fd: u64, length: u64) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe {
            libc::ftruncate(kernel_fd, length as i64)
        }
    }

    //------------------TRUNCATE SYSCALL------------------
    /*
    *   truncate() will return 0 when sucess, -1 when fail 
    */
    pub fn truncate_syscall(&self, path: &str, length: u64) -> i32 {
        let (path_c, _, _) = path.to_string().into_raw_parts();
        unsafe {
            libc::truncate(path_c as *const i8, length as i64)
        }
    }

    //------------------PIPE SYSCALL------------------
    pub fn pipe_syscall(&self, pipefd: &mut PipeArray) -> i32 {
        self.pipe2_syscall(pipefd, 0)
    }

    pub fn pipe2_syscall(&self, pipefd: &mut PipeArray, flags: i32) -> i32 {
        let flagsmask = O_CLOEXEC | O_NONBLOCK;
        let actualflags = flags & flagsmask;

        let pipe = interface::RustRfc::new(interface::new_pipe(PIPE_CAPACITY));

        // get an fd for each end of the pipe and set flags to RD_ONLY and WR_ONLY
        // append each to pipefds list

        let accflags = [O_RDONLY, O_WRONLY];
        for accflag in accflags {
            let (fd, guardopt) = self.get_next_fd(None);
            if fd < 0 {
                return fd;
            }
            let fdoption = &mut *guardopt.unwrap();

            let _insertval = fdoption.insert(Pipe(PipeDesc {
                pipe: pipe.clone(),
                flags: accflag | actualflags,
                advlock: interface::RustRfc::new(interface::AdvisoryLock::new()),
            }));

            match accflag {
                O_RDONLY => {
                    pipefd.readfd = fd;
                }
                O_WRONLY => {
                    pipefd.writefd = fd;
                }
                _ => panic!("How did you get here."),
            }
        }

        0 // success
    }

    //------------------GETDENTS SYSCALL------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   getdents() will return:
    *   - the number of bytes read is returned, success
    *   - 0, EOF
    *   - -1, fail 
    */
    pub fn getdents_syscall(&self, virtual_fd: u64, dirp: *mut u8, bufsize: u64) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe {
            libc::getdents(kernel_fd, dirp, bufsize as )
        }
    }

    //------------------------------------GETCWD SYSCALL------------------------------------
    /*
    *   getcwd() will return:
    *   - a pointer to a string containing the pathname of the current working directory, success
    *   - null, fail 
    */
    pub fn getcwd_syscall(&self, buf: *mut u8, bufsize: u64) -> i32 {
        unsafe {
            libc::getcwd(buf as *mut i8, bufsize as usize) as i32
        }
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
            if 0 != (shmflg & SHM_RDONLY) {
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
