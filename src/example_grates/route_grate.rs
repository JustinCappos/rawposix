// Example grates
//
//
// route requests to different grates
//  ex: /tmp to imfs + others to lower level fs, etc.
//
//      We need a better API to support this example.  
//
//      - Encasement libary supports a way to save and restore sets of system
//          calls.  Grate A is instantiated with the pure API.   A dummy child
//          is forked from it and that API is saved.  Grate B is instantiated 
//          with the pure API.  A dummy child if forked from grate B and its
//          API is also saved.  The filter grate is forked with the pure API
//          and the APIs from the two dummy children are provided.  Note that
//          the filter grate must return its cageID / PID from fork for each
//          grate if it wants to make calls of its own to those grates.
//          
//


// *******************************************************************
// ***  This file contains the sketch of a filtering handler which ***
// *** divides up the calls that are made between different grates ***
// ***      THIS CODE WILL NOT RUN!  IT IS MEANT TO ILLUSTRATE     ***
// ***      MY THINKING ABOUT HOW SOMETHING LIKE THIS WOULD        ***
// ***      WORK.  WE WILL MAKE A WORKING GRATE ONCE WE            ***
// ***      UNDERSTAND THE INTERFACES AND CHALLENGES BETTER.       ***
// *******************************************************************


// I'm realizing this likely needs its own library.  The reason is that
// there is one tedious part: separating out the grate to route a request
// to by system call.  So, really, you just want to decide once for every
// creation of a fd, where to assign it, and thereafter all the calls for
// it should end up in the right place...  Manually annotating write, send,
// recv, fcntl, etc. is a pain in the butt.  Especially calls like mmap,
// select, etc. which put the fd in a weird spot or do other weird things...
use multigratelib;
use lind_3i;
use lind_3i::constants::*;
use lind_encasement;


/*********************** some multigratelib code *************************/


pub gratemap: HashMap<String:grate_syscalls>;


// This adds entries to the gratemap so that they can be called later
// by the other system calls.
pub fn initialize_grates(grates: Vec<String>,interface:...) {


    for gratename in grates {

        // create the dummy child, snatch its API, and stick it in the 
        // gratemap.  This lets us use it later.
        gratemap[gratename] = lind_encasement.dummy_initialize_grate_and_return_syscalls(gratename,interface);
    }

}

// For each individual call, I check to see where the fd is from and then I 
// route to this grate.  These can be private functions...
fn fcntl_handler(cageid: u64, targetcageid: u64, callid: u64, fd: u64, cmd: u64, arg3: u64, arg4: u64, arg5: u64, arg6: u64) -> u64 {
    //int fcntl(int fd, int cmd, ...); 

    // panic if doesn't exist...
    let gratename = fdtable.get_entry(targetcageid,fd).extradata;

    return makesyscall(gratename,targetcageid,callid,fd,cmd,arg3,arg4,arg5,arg6);
}

// Above is just an example.  There would be one for each call with a fd...
// Or, at least there is one for every call with a fd in a specific position.
// Some calls like dup, etc. also need special handling.


//***************** Code the grate author needs to write *******************


pub fn my_open_syscall(cageid: u64, targetcageid: u64, callid: u64, pathname: u64, flags: u64, mode: u64, _: u64, _: u64, _: u64) -> u64 {
    // int open(const char *pathname, int flags, mode_t mode */ 
    //

    // the max filename length is supposed to be 4096
    let mut localfn_buffer = vec!([0u8,4096]);

    lind_3i.icstrncpy(MY_CAGE_ID, localfn_buffer, targetcageid, pathname,4096);

    // I do my filtering here...
    if abs_path_santize(pathname).startswith("/tmp/") {
        let myfd = multigratelib::makesyscall("grate_a.rs",targetcageid,OPEN_SYSIDpathname,flags,mode);
        // All future calls with this fd, go to this grate...
        multigratelib::filterfd("grate_a.rs",targetcageid,myfd);
        return myfd;
    }
    else {
        let myfd = multigratelib::makesyscall("grate_b.rs",targetcageid,OPEN_SYSID,pathname,flags,mode);
        // All future calls with this fd, go to this grate...
        multigratelib::filterfd("grate_b.rs",targetcageid,myfd);
        return myfd;
    }

}




// This sets up interposition so that calls go the right place...
fn setup_interposition() {
    // This sets up the basic handlers and says unknown fds should return
    // EBADFD.  This is useful when all fds should be known to us.
    multigratelib::add_handler(syscallid::OPEN_SYSID, my_open_syscall);

    // You can also always route a call to a specific grate without needing
    // to write a function
    multigratelib::always_handle_with_grate(syscallid::PIPE_SYSID, "grate_a.rs");

    // You can also just block a certain way to crate FDs...
    multigratelib::block_call(syscallid::SOCKET_SYSID);

    lind_encasement.replace_syscalls(syscall_replacements);

}


fn main() {

    // Initialize these two grates and don't change the interface for them
    // by setting None (just use my interface)
    multigratelib::initialize_grates(["grate_A.rs","grate_B.rs",None);
    // The above is equivalent to calling the function two times (each with
    // one of the grates).  If we want to have different interfaces for them,
    // we can do it that way.

    // If I want to have things handled with my API, I could also pass
    // the empty string "" as an option.
    // For example: multigratelib::initialize_grates(["",None);



    // Now, onto the real children!
    lind_encasement::initialize_children_and_consume_thread();
    // Never reaches here!
}
