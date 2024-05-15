// Example grates
//
// pass through
//  ex: filter network calls by dest or file accesses by path, measure API
//      usage / do strace equivalent.
//
//  note:
//      With the ability to set the target cage ID, I don't need to do much to
//      support multi-tenancy.  I can just use the targetcageid to do this.
//
//


// This does the heavy lifting (such as there is any...)
use lind_encasement;

// This file contains a basic, example system call handler that just prints
// out the arguments

pub fn log_syscall(cageid: u64, targetcageid: u64, callid: u64, arg1: u64, arg2: u64, arg3: u64, arg4: u64, arg5: u64, arg6: u64) -> u64 {
    // do whatever we want to log here...
    println!("{cageid}, {targetcageid}, {callid}, {arg1}, {arg2}, {arg3}, {arg4}, {arg5}, {arg6}");

    // Note, we don’t need to ensure the cageid can do an op 
    // on the targetcage because 3i checks that for us.  Nice!   
  
    // ...and make the original system call!
    return MAKE_SYSCALL(targetcageid, callid, arg1, cleaned_up_ptr_arg, count_as_u64, arg4, arg5, arg6);
}


fn main() {

    // Replace all calls with the one given here...
    lind_encasement.replace_all_syscalls(log_syscall);

    // instantiate child cage(s) as is needed here...
    lind_encasement.initialize_children_and_consume_thread();
    // Never reaches here!
}
