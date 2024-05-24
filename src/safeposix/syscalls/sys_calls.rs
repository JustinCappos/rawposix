#![allow(dead_code)]

// System related system calls
use super::fs_constants::*;
use super::net_constants::*;
use super::sys_constants::*;
use crate::interface;
use crate::safeposix::cage::*;

use crate::example_grates::fdtable::*;
use libc::*;

use std::sync::Arc as RustRfc;

impl Cage {

    pub fn fork_syscall(&self, child_cageid: u64) -> i32 {
        // Modify the fdtable manually 
        copy_fdtable_for_cage(self.cageid, child_cageid).unwrap();

        let cageobj = Cage {
            cageid: child_cageid,
            parent: self.cageid,
            // This happens because self.getgid tries to copy atomic value which does not implement "Copy" trait; self.getgid.load returns i32.
            getgid: interface::RustAtomicI32::new(
                self.getgid.load(interface::RustAtomicOrdering::Relaxed),
            ),
            getuid: interface::RustAtomicI32::new(
                self.getuid.load(interface::RustAtomicOrdering::Relaxed),
            ),
            getegid: interface::RustAtomicI32::new(
                self.getegid.load(interface::RustAtomicOrdering::Relaxed),
            ),
            geteuid: interface::RustAtomicI32::new(
                self.geteuid.load(interface::RustAtomicOrdering::Relaxed),
            ),
            thread_table: interface::RustHashMap::new(),
            main_threadid: interface::RustAtomicU64::new(0),
        };

        interface::cagetable_insert(child_cageid, cageobj);

        unsafe { libc::fork() }
    }

    /*
    *   exec() will only return if error happens 
    */
    pub fn exec_syscall(&self, child_cageid: u64) -> i32 {
        interface::cagetable_remove(self.cageid);

        // Delete all fd marked with FD_CLOEXEC
        let newfdtable = empty_fds_for_exec(self.cageid);

        // Delete the original one
        let _ = remove_cage_from_fdtable(self.cageid);
        // Add the new one to fdtable
        add_cage_to_fdtable(self.cageid, newfdtable);

        let newcage = Cage {
            cageid: child_cageid,
            parent: self.parent,
            getgid: interface::RustAtomicI32::new(-1),
            getuid: interface::RustAtomicI32::new(-1),
            getegid: interface::RustAtomicI32::new(-1),
            geteuid: interface::RustAtomicI32::new(-1),
            thread_table: interface::RustHashMap::new(),
            main_threadid: interface::RustAtomicU64::new(0),
        };
        //wasteful clone of fdtable, but mutability constraints exist

        interface::cagetable_insert(child_cageid, newcage);
        
        unsafe { libc::execl() } // Which function should we call?
    }

    pub fn exit_syscall(&self, status: i32) -> i32 {
        //flush anything left in stdout
        interface::flush_stdout();

        //may not be removable in case of lindrustfinalize, we don't unwrap the remove result
        interface::cagetable_remove(self.cageid);

        // Trigger SIGCHLD
        if !interface::RUSTPOSIX_TESTSUITE.load(interface::RustAtomicOrdering::Relaxed) {
            // dont trigger SIGCHLD for test suite
            if self.cageid != self.parent {
                interface::lind_kill_from_id(self.parent, libc::SIGCHLD);
            }
        }

        //fdtable will be dropped at end of dispatcher scope because of Arc
        status
    }

    pub fn getpid_syscall(&self) -> i32 {
        unsafe { libc::getpid() }
        // self.cageid as i32 //not sure if this is quite what we want but it's easy enough to change later
    }
    pub fn getppid_syscall(&self) -> i32 {
        unsafe { libc::getppid() }
        // self.parent as i32 // mimicing the call above -- easy to change later if necessary
    }

    /*if its negative 1
    return -1, but also set the values in the cage struct to the DEFAULTs for future calls*/
    pub fn getgid_syscall(&self) -> u32 {
        unsafe { libc::getgid() }
    }
    pub fn getegid_syscall(&self) -> u32 {
        unsafe { libc::getegid() }
    }

    pub fn getuid_syscall(&self) -> u32 {
        unsafe { libc::getuid() }
    }
    pub fn geteuid_syscall(&self) -> u32 {
        unsafe { libc::geteuid() }
    }

    pub fn sigaction_syscall(
        &self,
        sig: u64,
        act: *const sigaction,
        oact: *mut sigaction
    ) -> i32 {
        unsafe { libc::sigaction(sig as i32, act, oact) }
    }

    pub fn kill_syscall(&self, cage_id: i32, sig: i32) -> i32 {
        if (cage_id < 0) || (cage_id >= interface::MAXCAGEID) {
            return syscall_error(Errno::EINVAL, "sigkill", "Invalid cage id.");
        }

        if let Some(cage) = interface::cagetable_getref_opt(cage_id as u64) {
            interface::lind_threadkill(
                cage.main_threadid
                    .load(interface::RustAtomicOrdering::Relaxed),
                sig,
            );
            return 0;
        } else {
            return syscall_error(Errno::ESRCH, "kill", "Target cage does not exist");
        }
    }

    pub fn sigprocmask_syscall(
        &self,
        how: u64,
        set: *const sigset_t,
        oldset: *mut sigset_t,
    ) -> i32 {
        unsafe { libc::sigprocmask(how as i32, set, oldset) }
    }

    /* NOT FOUND IN RUST LIBC */
    // pub fn setitimer_syscall(
    //     &self,
    //     which: i32,
    //     new_value: Option<&interface::ITimerVal>,
    //     old_value: Option<&mut interface::ITimerVal>,
    // ) -> i32 {
    //     match which {
    //         ITIMER_REAL => {
    //             if let Some(some_old_value) = old_value {
    //                 let (curr_duration, next_duration) = self.interval_timer.get_itimer();
    //                 some_old_value.it_value.tv_sec = curr_duration.as_secs() as i64;
    //                 some_old_value.it_value.tv_usec = curr_duration.subsec_millis() as i64;
    //                 some_old_value.it_interval.tv_sec = next_duration.as_secs() as i64;
    //                 some_old_value.it_interval.tv_usec = next_duration.subsec_millis() as i64;
    //             }

    //             if let Some(some_new_value) = new_value {
    //                 let curr_duration = interface::RustDuration::new(
    //                     some_new_value.it_value.tv_sec as u64,
    //                     some_new_value.it_value.tv_usec as u32,
    //                 );
    //                 let next_duration = interface::RustDuration::new(
    //                     some_new_value.it_interval.tv_sec as u64,
    //                     some_new_value.it_interval.tv_usec as u32,
    //                 );

    //                 self.interval_timer.set_itimer(curr_duration, next_duration);
    //             }
    //         }

    //         _ => { /* ITIMER_VIRTUAL and ITIMER_PROF is not implemented*/ }
    //     }
    //     0
    // }

    pub fn getrlimit(&self, res_type: u64, rlimit: *mut rlimit) -> i32 {
       unsafe { libc::getrlimit(res_type as i32, rlimit as *mut rlimit)}
    }

    pub fn setrlimit(&self, res_type: u64, limit_value: *const rlimit) -> i32 {
        unsafe { libc::setrlimit(res_type as i32, limit_value) }
    }
}
