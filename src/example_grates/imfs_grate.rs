// Example grates
//
// handle file requests internally (need inode / dir, fd table) 
//  ex: in memory file system, network file system, separate /tmp per-process,
//      lindfs
//
//  note:
//      it's slightly odd I need a fd table here.  I guess it is custom to the
//      grate though.  
//

// *******************************************************************
// ***    This file contains the sketch of Lind's in memory fs     ***
// ***      THIS CODE WILL NOT RUN!  IT IS MEANT TO ILLUSTRATE     ***
// ***      MY THINKING ABOUT HOW SOMETHING LIKE THIS WOULD        ***
// ***      WORK.  WE WILL MAKE A WORKING GRATE ONCE WE            ***
// ***      UNDERSTAND THE INTERFACES AND CHALLENGES BETTER.       ***
// *******************************************************************




use lind_encasement;
use lind_3i;
use lind_3i::constants::*;

// I'm going to include this, which will use fdtable extensively...
use virt_fsmetadata;

/**************** virt_fsmetadata selected exerpts  *****************/

pub struct data_storage_interface {
    pub fn create_item(item_id:u64);
    pub fn open_item(item_id:u64);
    pub fn close_item(item_id:u64);
    pub fn store_data(targetcage: u64, item_id:u64, position:u64; data: *[u8], length:u64) -> Result<...>;
    pub fn read_data(targetcage: u64, item_id:u64, position:u64; data: *[u8], amount:u64) -> Result<...>;
    // could implement or add others...
    pub fn log_action(...);


};

// I'm assuming that we always know all of the metadata because we virtualize
// it.  This means we know the size of every file, etc. 

/*** All the inode, data structure code goes here...  ***/



// We hook in the handlers for read, write, etc.
pub fn setup_interposition(calls_to_integrate:data_storage_interface) {
    // The encasement library will help w/ syscall replacements for my children
    let mut syscall_replacements: Vec<lind_encasement::repltable> = Vec::new();

    // I handle all open calls, etc...
    syscall_replacements.push(repltable{syscallid:PIPE_SYSID, func:open_syscall});

    // Let's handle read and write...
    syscall_replacements.push(repltable{syscallid:READ_SYSID, func:read_syscall});
    syscall_replacements.push(repltable{syscallid:WRITE_SYSID, func:write_syscall});

    syscall_replacements.push(repltable{syscallid:MMAP_SYSID, func:mmap_syscall});
    // And so on until we have all the file system calls...
    
    //... until finally
    lind_encasement.replace_syscalls(syscall_replacements);
}

// I'm assuming that how the above calls are used is quite self-evident.  
// In essence, we just have the existing interface for most things, but the
// above extracts out the file storage.

// This gets overridden...  As would related calls like munmap()
pub fn mmap_syscall() {
    ...
}


pub fn initialize_fs_metadata() {
    // I'll either make this fresh or read it in here...
    ...
}


// The code here keeps a fdtable, inode information, directory information,
// etc, much the same way as the existing code.  When we open something (which
// is not open), we call open_item




/**************** Unique code for this implementation ***************/

pub fn init_imfs() {
    // Create a global data structure which allocates in memory blocks to store
    // the things it needs to persist.
}


pub fn my_create_item(item_id:u64) {
    // create an entry in the item table.  The value stored is the fd.

    if item_id in itemtable {
        panic!("Item already open");
    }
    // Ensure we are creating this item or panic!
    itemtable[item_id] = _make_block_list();
}


pub fn my_store_data(targetcageid: u64, item_id:u64, position:u64; data: *[u8], length:u64) -> Result<...> {

    // This is my custom way to handle storing metadata...
    let mut source_data_pos = data;

    let currentlength = length;
    // loops through while getting and/or locating blocks
    while currentlength > 0 {
        let blockptr,allowedamount = _alloc_or_get_block_address(itemtable[item_id],position,currentlength);
        lind_3i.read_from_cage(targetcageid, source_data_pos, blockptr, allowedamount);
        currentlength -= allowedamount;
        source_data_pos += allowedamount;

    }
    return length;
}


pub fn my_read_data(targetcageid: u64, item_id:u64, position:u64; data: *[u8], amount:u64) -> Result<...> {
    // This is my custom way to handle reading in data...

    let mut writedatapos = data;
    // Walk through the blocks and use 
    for blockpos,length in _get_block_location_iter(item_id,position,amount) {
        lind_3i.write_to_cage(targetcageid,blockpos, writedatapos,length);
        writedatapos +=length;
    }

    // I always return it all (?virt_metadata tracks the length?)
    return amount;
}


// I'm going to interpose here, so I need to have the full interface...
pub fn my_mmap_syscall(cageid: u64, targetcageid: u64, callid: u64, addr: u64, length: u64, prot: u64, flags: u64, fd: u64, offset: u64) -> u64 {
    // *mmap(void addr[.length], size_t length, int prot, int flags, int fd, off_t offset);

    // do I need to call their code to set anything up, like file descriptors?

    
    if ! MAP_ANONYMOUS & flags {
        // If this is file-backed, I would loop through and allocate the 
        // blocks, much like with my_store_data(...).

    }
    else { // MAP_ANONYMOUS
        // I probably don't understand all the nuances of ANONYMOUS mapping,
        // but I'm assuming I can just zero out the blocks of memory...
        if flags & MAP_PRIVATE {
            // if not shared, likely okay to just do nothing but zero the
            // memory...
            return...;
        }
        // I'm not sure how to handle MAP_SHARED.  Likely need to set up the
        // shared memory mapping on fork...
        // However, we don't currently handle this in lindfs...
    }

    
    // Now I loop through and allocated shared memory for each block so that
    // it is mapped from my cache into the cage's memory...

}

// munmap is similar, but easier.  Just removes memory mappings...


// We probably need to do something on fork so that we can handle mmap 
// correctly...
pub fn my_fork_syscall(cageid: u64, targetcageid: u64, callid: u64, addr: u64, length: u64, prot: u64, flags: u64, fd: u64, offset: u64) -> u64 {

    // Need to handle MAP_SHARED mappings here, so they are mapped shared
    // into the child
}




fn main() {
    // Setup my item table...
    init_item_table();

    // Have the virtual_fs initialize itself...
    virt_metadata.initialize_fs_metadata();

    // Register my calls
    let mycalls = virt_metadata::data_storage_interface {
        create_item: my_create_item,
        open_item: virt_metadata::NOOP,
        close_item: virt_metadata::NOOP,
        store_data: my_store_data,
        read_data: my_read_data,
        // could implement or add others...
        log_action:virt_metadata::DEFAULT,
        // Don't persist metadata, since it's an imfs...
        store_directories:false,
        store_inodes:false,
    };


    // need to replace calls with the right ones for our children
    virt_metadata.setup_interposition(mycalls);

    // Need to instantiate child cage(s) here...  
    lind_encasement.initialize_children_and_consume_thread();
    // Never reaches here!
}
