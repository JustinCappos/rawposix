
//
// custom handle non-file requests internally (fd table)
//  ex: in memory pipes, loopback sockets, unix domain sockets, etc.  
//
//  note:
//      How do I reserve the fd I need here?  Do I have a call to reserve a fd?
//      If so, I likely need a way to close or release it as well...
//      I also should keep a fd table to see how to handle this...
//

// *******************************************************************
// ***  This file contains the sketch of an in-memory pipe handler ***
// ***      THIS CODE WILL NOT RUN!  IT IS MEANT TO ILLUSTRATE     ***
// ***      MY THINKING ABOUT HOW SOMETHING LIKE THIS WOULD        ***
// ***      WORK.  WE WILL MAKE A WORKING GRATE ONCE WE            ***
// ***      UNDERSTAND THE INTERFACES AND CHALLENGES BETTER.       ***
// *******************************************************************

use fdtable;
use lind_3i;
use lind_3i::constants::*;
use lind_encasement;


// Initialize the circular buffers for the in memory pipes
def init_circular_buffer_table() {
    // do whatever initialization I need to for the circular buffers...
}

// handle pipe creation
pub fn my_pipe_syscall(cageid: u64, targetcageid: u64, callid: u64, pipefd: u64, _: u64, _: u64, _: u64, _: u64, _: u64) -> u64 {
    // int pipe(int pipefd[2]);

    let read_fd = lind_3i::reserve_fd(targetcageid,None);
    let write_fd = lind_3i::reserve_fd(targetcageid,None);
    // size of a file descriptor in bytes...
    const FD_SIZE = 4;

    // Adds an entry to the table with:
    //      cage
    //      fd
    //      flags
    //      mode
    //      position
    //      extra_data
    fdtable::add_entry(targetcageid,read_fd,0,O_RDONLY,0,None);
    fdtable::add_entry(targetcageid,write_fd,0,O_WRONLY,0,None);

    // Writing the fds back to the child...
    lind_3i::write_to_cage(targetcageid,pipefd,read_fd,FD_SIZE);
    pipefd += FD_SIZE;
    lind_3i::write_to_cage(targetcageid,pipefd,write_fd,FD_SIZE);

    // No need to call below me...

    // Return success!
    return 0;
    
}

pub fn my_read_syscall(cageid: u64, targetcageid: u64, callid: u64, fd: u64, buf: u64, count: u64, _: u64, _: u64, _: u64) -> u64 {
    // ssize_t read(int fd, void buf[.count], size_t count);


    /***** Read from the circular buffer, block, etc. here... *****/
    lind_3i::write_to_cage(targetcageid,buf,local_buffer,count);


    return count;

    /**** End specific pipe logic */
    
}

pub fn my_write_syscall(cageid: u64, targetcageid: u64, callid: u64, fd: u64, buf: u64, count: u64, _: u64, _: u64, _: u64) -> u64 {
    // ssize_t write(int fd, const void buf[.count], size_t count);


    /***** Write to the circular buffer, block, etc. here... *****/
    lind_3i::read_from_cage(targetcageid,local_buffer,buf,count);


    return count;

    /**** End specific pipe logic */
    
}


pub fn my_close_syscall(cageid: u64, targetcageid: u64, callid: u64, fd: u64, buf: u64, count: u64, _: u64, _: u64, _: u64) -> u64 {
    //  int close(int fd);

    /***** clean up the buffer, if needed   ****/

    return 0;

    /**** End specific pipe logic */
    
}

pub fn my_select_helper(targetcageid: u64, callid: u64, fdvec: Vec<u64>) -> Vec<u64,status> {
    // Select, poll, etc. are a bit of a mess.  Maybe it makes sense to have
    // a helper instead?

    /* call with a vector of file descriptors and returns an vector of fds 
     * with an enum with a statue for each POLLERR, POLLHUP, POLLIN, POLLOUT
     * etc.
     */


    return ...;

    /**** End specific pipe logic */
    
}












/************** Example pseudocode from the fdtable code *****************/

pub fn fork_syscall(cageid: u64, targetcageid: u64, callid: u64, arg1: u64, arg2: u64, arg3: u64, arg4: u64, arg5: u64, arg6: u64) -> u64 {
    // int fork();
    let newcageid= lind_encasement::handle_fork(targetcageid);

    // Make a copy of the parent's FD table...
    _dup_row(targetcageid,newcageid);
    return newcageid;

}

pub fn exec_syscall(cageid: u64, targetcageid: u64, callid: u64, arg1: u64, arg2: u64, arg3: u64, arg4: u64, arg5: u64, arg6: u64) -> u64 {

    // close fds that were close on exec...
    _handle_cloexec(targetcageid);

    return MAKE_SYSCALL(targetcageid, callid, arg1, arg2, arg3, arg4, arg5, arg6);

}


// This is the basic logic for all of the system calls that fdtable handles.
// It decides where to route things...
pub fn route_syscall(cageid: u64, targetcageid: u64, callid: u64, arg1: u64, arg2: u64, arg3: u64, arg4: u64, arg5: u64, arg6: u64) -> u64 {
    // close(fd);

    if _fd_table_in(targetcageid,arg1) {
        // Call handler just calls the appropriate system call function from
        // the table...
        return call_handler(cageid,targetcageid, callid, arg1,arg2,arg3,arg4,arg5,arg6)
    else {
        // Call beneath us...
        return MAKE_SYSCALL(targetcageid, callid, arg1, arg2, arg3, arg4, arg5, arg6);
    }

}

pub fn boilerplate_init_for_fdtables(Vec <lind_encasement::repltable>) {

    // Let fdtable handle these (and likely I need to add others...  This 
    // most likely would be handled for me via a function call to initialize
    // these at the same time instead of me doing it individually...
    syscall_replacements::push(repltable{syscallid:FORK_SYSID, func:fdtable::fork_syscall});
    syscall_replacements::push(repltable{syscallid:EXEC_SYSID, func:fdtable::exec_syscall});
    syscall_replacements::push(repltable{syscallid:DUP_SYSID, func:fdtable::dup_syscall});
    syscall_replacements::push(repltable{syscallid:DUP2_SYSID, func:fdtable::dup2_syscall});

    // Ignore open because we don't care about files...  If we handled named
    // pipes, we would add open...
//    syscall_replacements::push(repltable{syscallid:OPEN_SYSID, func:lind_encasement::DEFAULT});

}

/*************************** MAIN *******************************/

 

// This sets up the calls so that the right things are interposed...
fn setup_interposition() {
    // The encasement library will help w/ syscall replacements for my children
    let mut syscall_replacements: Vec<lind_encasement::repltable> = Vec::new();

    // This sets up basic handlers, and says unknown fds should call to the
    // grate below...  This is useful when we only want to intercept some calls
    // but do want to pass others through.
    boilerplate_init_for_fdtables(syscall_replacements,CALLDOWN);

    // I handle all pipe calls in my own code...
    syscall_replacements::push(repltable{syscallid:PIPE_SYSID, func:my_pipe_syscall});

    // Let's handle read and write...
    syscall_replacements::push(repltable{syscallid:READ_SYSID, func:fdtable::read_syscall});
    // add my handler for read.  Will only be called on fds I added to the 
    // table.  Other FDs will call below...
    fdtable::add_handler(syscallid::READ_SYSID, my_read_syscall);
    syscall_replacements::push(repltable{syscallid:WRITE_SYSID, func:fdtable::write_syscall});
    fdtable::add_handler(syscallid::WRITE_SYSID, my_write_syscall);

    // add my handler for close.  Only called on my fds
    syscall_replacements::push(repltable{syscallid:CLOSE_SYSID, func:fdtable::close_syscall});
    fdtable::add_handler(syscallid::CLOSE_SYSID, my_close_syscall);


    // This handles select, poll, etc. in a clean way.  Only called for my fds
    fdtable::add_select_helper(my_select_helper);


    lind_encasement::replace_syscalls(syscall_replacements);

}


fn main() {
    // do my setup...  Where does this live?  Rust doesn't like globals,
    // but I need to share this...
    fdtable::get_new_table();

    // If I'm setting up circular buffers, do it here...
    init_circular_buffer_table();
    
    // need to replace calls with the right ones for our children
    setup_interposition();

    // Need to instantiate child cage(s) here...  
    lind_encasement::initialize_children_and_consume_thread();
    // Never reaches here!
}
