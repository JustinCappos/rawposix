#![allow(dead_code)]

// File system related system calls
use super::fs_constants::*;
use super::sys_constants::*;
use crate::interface;
use crate::safeposix::cage::Errno::EINVAL;
use crate::safeposix::cage::*;
// use crate::safeposix::filesystem::*;
// use crate::safeposix::net::NET_METADATA;
// use crate::safeposix::shm::*;

use libc::*;
use std::os::unix::io::RawFd;

use crate::example_grates::fdtable::*;

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
    pub fn fstat_syscall(&self, virtual_fd: i32, statbuf: &mut stat) -> i32 {
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
    pub fn fstatfs_syscall(&self, virtual_fd: i32, databuf: &mut statfs) -> i32 {
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
    pub fn read_syscall(&self, virtual_fd: i32, readbuf: *mut u8, count: u64) -> i32 {
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
    pub fn pread_syscall(&self, virtual_fd: i32, buf: *mut u8, count: u64, offset: u64) -> i32 {
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
    pub fn write_syscall(&self, virtual_fd: i32, buf: *const u8, count: u64) -> i32 {
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
    pub fn pwrite_syscall(&self, virtual_fd: i32, buf: *const u8, count: u64, offset: u64) -> i32 {
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
    pub fn lseek_syscall(&self, virtual_fd: i32, offset: u64, whence: u64) -> i32 {
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
    pub fn fchdir_syscall(&self, virtual_fd: i32) -> i32 {
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
    /* 
    *   dup() / dup2() will return a file descriptor 
    *   Mapping a new virtual fd and kernel fd that libc::dup returned
    *   Then return virtual fd
    */
    pub fn dup_syscall(&self, virtual_fd: i32, _start_desc: Option<i32>) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        let ret_kernelfd = unsafe{ libc::dup(kernel_fd) };
        let ret_virtualfd = get_unused_virtual_fd(self.cageid, ret_kernelfd, false, 0).unwrap();
        ret_virtualfd
    }

    /* 
    */
    pub fn dup2_syscall(&self, old_virtualfd: i32, new_virtualfd: i32) -> i32 {
        let old_kernelfd = translate_virtual_fd(self.cageid, old_virtualfd).unwrap();
        let new_kernelfd = unsafe {
            libc::dup(old_kernelfd as i32)
        };
        // Map new kernel fd with provided kernel fd
        let _ret_kernelfd = unsafe{ libc::dup2(old_kernelfd, new_kernelfd) };
        let optinfo = get_optionalinfo(self.cageid, old_virtualfd).unwrap();
        let _ = get_specific_virtual_fd(self.cageid, new_virtualfd, new_kernelfd, false, optinfo).unwrap();
        new_virtualfd
    }

    //------------------------------------CLOSE SYSCALL------------------------------------
    /*
    *   Get the kernel fd with provided virtual fd first
    *   close() will return 0 when sucess, -1 when fail 
    */
    pub fn close_syscall(&self, virtual_fd: i32) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        // Remove file descriptor from virtual fdtable
        let _ = rm_virtual_fd(self.cageid, virtual_fd).unwrap();
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
    pub fn fcntl_syscall(&self, virtual_fd: i32, cmd: u64, arg: u64) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        if (cmd as i32) == libc::F_DUPFD {
            let new_kernelfd = unsafe { libc::fcntl(kernel_fd, cmd as i32, arg) };
            // Get status
            let new_virtualfd = get_unused_virtual_fd(self.cageid, new_kernelfd, false, 0).unwrap();
            return new_virtualfd as i32;
        }
        unsafe { libc::fcntl(kernel_fd, cmd as i32, arg) }
    }

    //------------------------------------IOCTL SYSCALL------------------------------------
    /*
    *   The third argument is an untyped pointer to memory.  It's traditionally char *argp 
    *   (from the days before void * was valid C), and will be so named for this discussion.
    *   ioctl() will return 0 when success and -1 when fail. 
    *   Note: A few ioctl() requests use the return value as an output parameter and return 
    *   a nonnegative value on success.
    */
    pub fn ioctl_syscall(&self, virtual_fd: i32, request: u64, ptrunion: IoctlPtrUnion) -> i32 {
        let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
        unsafe { libc::ioctl(kernel_fd, request, ptrunion as *mut _ as *mut c_void) }
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
    pub fn fchmod_syscall(&self, virtual_fd: i32, mode: u64) -> i32 {
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
        virtual_fd: i32,
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
    pub fn flock_syscall(&self, virtual_fd: i32, operation: u64) -> i32 {
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
    pub fn fsync_syscall(&self, virtual_fd: i32) -> i32 {
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
    pub fn fdatasync_syscall(&self, virtual_fd: i32) -> i32 {
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
        virtual_fd: i32,
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
    pub fn ftruncate_syscall(&self, virtual_fd: i32, length: i64) -> i32 {
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
    /*
    *   When using the rust libc, a pipe file descriptor (pipefd) is typically an array 
    *   containing two integers. This array is populated by the pipe system call, with one 
    *   integer for the read end and the other for the write end.
    *
    *   pipe() will return 0 when sucess, -1 when fail 
    */
    pub fn pipe_syscall(&self, pipefd: &[i32]) -> i32 {
        let mut kernel_fds = Vec::with_capacity(2);
        for index in 0..2 {
            let virtual_fd = pipefd[index];
            let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
            kernel_fds.push(kernel_fd);
        }
        unsafe { libc::pipe(kernel_fds.as_mut_ptr() as *mut i32) }
    }

    pub fn pipe2_syscall(&self, pipefd: &[i32], flags: u64) -> i32 {
        let mut kernel_fds = Vec::with_capacity(2);
        for index in 0..2 {
            let virtual_fd = pipefd[index];
            let kernel_fd = translate_virtual_fd(self.cageid, virtual_fd).unwrap();
            kernel_fds.push(kernel_fd);
        }
        unsafe { libc::pipe2(kernel_fds.as_mut_ptr() as *mut i32, flags as i32) }
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
    pub fn getcwd_syscall(&self, buf: *mut u8, bufsize: u64) -> i32 {
        unsafe {
            libc::getcwd(buf as *mut i8, bufsize as usize) as i32
        }
    }

    //------------------SHMGET SYSCALL------------------
    /* 
    *   shmget() will return:
    *   - a valid shared memory identifier, success
    *   - -1, fail
    */
    pub fn shmget_syscall(&self, key: u64, size: u64, shmflg: u64) -> i32 {
        unsafe { libc::shmget(key as i32, size as usize, shmflg as i32) as i32 }
    }

    //------------------SHMAT SYSCALL------------------
    /* 
    *   shmat() will return:
    *   - the segment's start address, success
    *   - -1, fail    
    */
    pub fn shmat_syscall(&self, shmid: u64, shmaddr: *mut u8, shmflg: u64) -> i32 {
        // Convert address to adapt to NaCl
        ((unsafe { libc::shmat(shmid as i32, shmaddr as *const c_void, shmflg as i32)} as i64 ) & 0xffffffff) as i32
    }

    //------------------SHMDT SYSCALL------------------
    /* 
    *   shmdt() will return 0 when sucess, -1 when fail 
    */
    pub fn shmdt_syscall(&self, shmaddr: *mut u8) -> i32 {
        unsafe { libc::shmdt(shmaddr as *const c_void) }
    }

    pub fn shmctl_syscall(&self, shmid: i32, cmd: i32, buf: *mut shmid_ds) -> i32 {
        unsafe { libc::shmctl(shmid, cmd, buf) }
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
    *   sem_init() will return 0 when sucess, -1 when fail 
    */
    pub fn sem_init_syscall(&self, sem: *mut sem_t, pshared: u64, value: u64) -> i32 {
        unsafe{ libc::sem_init(sem, pshared as i32, value as u32) }
    }

    /*
    *   sem_wait() will return 0 when sucess, -1 when fail 
    */
    pub fn sem_wait_syscall(&self, sem: *mut sem_t) -> i32 {
        unsafe{ libc::sem_wait(sem) }
    }

    /*
    *   sem_post() will return 0 when sucess, -1 when fail 
    */
    pub fn sem_post_syscall(&self, sem: *mut sem_t) -> i32 {
        unsafe{ libc::sem_post(sem) }
    }

    /*
    *   sem_destroy() will return 0 when sucess, -1 when fail 
    */
    pub fn sem_destroy_syscall(&self, sem: *mut sem_t) -> i32 {
        unsafe{ libc::sem_destroy(sem) }
    }

    /*
    *   sem_getvalue() will return 0 when sucess, -1 when fail 
    */
    pub fn sem_getvalue_syscall(&self, sem: *mut sem_t, sval: u64) -> i32 {
        unsafe{ libc::sem_getvalue(sem, sval as i32) }
    }

    /*
    *   sem_trywait() will return 0 when sucess, -1 when fail 
    */
    pub fn sem_trywait_syscall(&self, sem: *mut sem_t) -> i32 {
       unsafe{ libc::sem_trywait(sem) }
    }

    /*
    *   sem_timedwait() will return 0 when sucess, -1 when fail 
    */
    pub fn sem_timedwait_syscall(&self, sem: *mut sem_t, abstime: *const timespec) -> i32 {
        unsafe{ libc::sem_timedwait(sem, abstime) }
    }
}
