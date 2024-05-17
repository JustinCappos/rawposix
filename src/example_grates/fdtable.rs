// This is a basic fdtables library.  The purpose is to allow a cage to have
// a set of virtual fds which is translated into real fds.  
//
// For example, suppose a cage with cageid A, wants to open a file.  That open
// operation needs to return a file descriptor to the cage.  Rather than have
// each cage have the actual underlying numeric fd[*], each cage has its own 
// virtual fd numbers.  So cageid A's fd 6 will potentially be different from
// cageid B's fd 6.  When a call from cageid A or B is made, this will need to
// be translated from that virtual fd into the read fd[**].
//
// One other complexity deals with the CLOEXEC flag.  If this is set on a file
// descriptor, then when exec is called, it must be closed.  This library 
// provides a few functions to simplify this process.
//
// To make this work, this library provides the following funtionality:
//
//      translate_virtual_fd(cageid, virtualfd) -> Result<realfd,EBADFD>
//      get_unused_virtual_fd(cageid,realfd,is_cloexec,optionalinfo) -> Result<virtualfd, EMFILE>
//      set_cloexec(cageid,virtualfd,is_cloexec) -> Result<(), EBADFD>
//
//
// There are other helper functions:
//  
//      get_optionalinfo(cageid,virtualfd) -> Result<optionalinfo, EBADFD>
//      set_optionalinfo(cageid,virtualfd,optionalinfo) -> Result<(), EBADFD>
//          The above two are useful if you want to track other things like
//          an id for other in-memory data structures
//
//      copy_fdtable_for_cage(srccageid, newcageid) -> Result<(), ENFILE>
//          This is mostly used in handling fork, etc.  
//
//      remove_cage_from_fdtable(cageid) 
//          This is mostly used in handling exit, etc.
//
//      close_all_for_exec(cageid) 
//          This handles exec by removing all of the realfds from the cage.
//
//      get_exec_iter(cageid) -> iter()
//          This handles exec by returning an iterator over the realfds,
//          removing each entry after the next iterator element is returned.
//
// In situations where this will be used by a grate, a few other calls are
// particularly useful:
//      
//      lind_3i::reserve_fd(cageid, Option<fd>) -> Result<fd, EMFILE / ENFILE>
//          Used to have the grate, etc. beneath you reserve (or provide) a fd.
//          This is useful for situatiosn where you want to have most fds
//          handled elsewhere, but need to be able to acquire a few for your
//          purposes (like implementing in-memory pipes, etc.)
//
// [*] This isn't possible because fork causes the same fd in the parent and
// child to have separate file pointers (e.g., read / write to separate 
// locations in the file.
//
// [**] This is only the 'real' fd from the standpoint of the user of this
// library.  If another part of the system below it, such as another grate or
// the microvisor, is using this library, it will get translated again.
//


// This library is likely the place in the system where we should consider
// putting in place limits on file descriptors.  Linux does this through two
// error codes, one for a per-process limit and the other for an overall system
// limit.  My thinking currently is that both will be configurable values in
// the library.  
//
//       EMFILE The per-process limit on the number of open file
//              descriptors has been reached.
//
//       ENFILE The system-wide limit on the total number of open files
//              has been reached.


// We will raise a panic anywhere we receive an unknown cageid.  This frankly
// should not be possible and indicates some sort of internal error in our
// code.  However, it is expected we could receive an invalid file descriptor
// when a cage makes a call.  



#![feature(lazy_cell)]

use std::collections::HashMap;

use std::sync::LazyLock;

// In order to store this information, I'm going to use a HashMap which
// has keys of (cageid:u64) and values that are another HashMap.  The second
// HashMap has keys of (virtualfd:64) and values of (realfd:u64,
// should_cloexec:bool, optionalinfo:u64). 
//
// To speed up lookups, I could have used arrays instead of HashMaps.  In 
// theory, that space is far too large, but likely each could be bounded to 
// smaller values like 1024.  For simplicity I avoided this for now.
//
// I thought also about having different tables for the tuple of values
// since they aren't always used together, but this seemed needlessly complex
// (at least at first).
//
// I'm using LazyLock because I think this is how I'm supposed to set up 
// static / global variables.
static fdtable: LazyLock<HashMap<u64, HashMap<u64,fdtableentry>>> = LazyLock::new(|| {
    let mut m = HashMap::new();
    // How do I initialize the first cage?  When does this happen?
    m
});

// These are the values we look up with at the end...
struct fdtableentry {
    realfd:u64, // underlying fd (may be a virtual fd below us or a kernel fd)
    should_cloexec:bool, // should I close this when exec is called?
    optionalinfo:u64, // user specified / controlled data
}


//      translate_virtual_fd(cageid, virtualfd) -> Result<realfd,EBADFD>
pub fn translate_virtual_fd(cageid:u64, virtualfd:u64) -> Result<realfd:u64,EBADFD> {
    // They should not be able to pass a new cage I don't know.  I should
    // always have a table for each cage because each new cage is added at fork
    // time
    let cagetable: HashMap<u64,fdtableentry> = fdtable.get(cageid).unwrap("Internal error, unknown cageid in translate_virtual_fd");

    return match cagetable.get(virtualfd) {
        Some(tableentry) => tableentry[0],
        None => EBADFD,
    }
}
//      get_unused_virtual_fd(cageid,realfd,is_cloexec,optionalinfo) -> Result<virtualfd, EMFILE>
//      set_cloexec(cageid,virtualfd,is_cloexec) -> Result<(), EBADFD>
