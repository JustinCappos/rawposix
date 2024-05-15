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
// ***  This file contains the sketch of Lind's safeposix_rust fs  ***
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

// NOTE: mmap in safeposix_rust just does some error checking and then calls
// down.  We can do the same here!
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

pub fn init_item_table() {
    // Create a global table of items here.  In this implementation, this
    // will map item_ids to fds of mine.
}


pub fn my_create_item(item_id:u64) {
    // create an entry in the item table.  The value stored is the fd.

    if item_id in itemtable {
        panic!("Item already open");
    }
    // Ensure we are creating this item or panic!
    itemtable[item_id] = open("linddata.{item_id}",O_CREAT|O_EXCL|O_RDWR,0o600).unwrap();
}


pub fn my_open_item(item_id:u64) {
    // create an entry in the item table.  The value stored is the fd.

    if item_id in itemtable {
        panic!("Item already open");
    }
    // Ensure we're opening an existing item or panic!
    itemtable[item_id] = open("linddata.{item_id}",O_RDWR,0o600).unwrap();

}

pub fn my_close_item(item_id:u64) {
    // create an entry in the item table.  The value stored is the fd.

    if !item_id in itemtable {
        panic!("Item is not open");
    }
    close(itemtable[item_id])

}

pub fn my_store_data(targetcage: u64, item_id:u64, position:u64; data: *[u8], length:u64) -> Result<...> {
    // This is my custom way to handle storing data...

    // I should never be past the end of the file since the virt_fs knows
    // the position and has checked it...

    let fd = itemtable[item_id];

    // I need to lock this... 
    {
   
        let last_pos = virt_fsmetadata.get_item_id_entry(item_id).position;

        if position != last_pos {
            lseek(fd, position);
        }
        // BUG: This fd is this cage's fd, while the data pointer is from the 
        // target cage.  This means that 3i needs to be able to support a mix
        // of cage associations for different arguments...  BUG BUG BUG
        let amt_written = MAKE_SYSCALL(targetcage, WRITE_SYSID, fd, data, length).unwrap();
        // do error handling, likely panic, since no error should occur...
    }
    return amt_written;  // To be used to update the position...
    
}


pub fn my_read_data(targetcage: u64, item_id:u64, position:u64; data: *[u8], amount:u64) -> Result<...> {
    // This is my custom way to handle reading in data...

    // Once again, I should never be past the end of the file, etc. since the 
    // virt_fs knows the position and has checked it...

    let fd = itemtable[item_id];

    // I need to lock this... 
    {
   
        let last_pos = virt_fsmetadata.get_item_id_entry(item_id).position;

        if position != last_pos {
            lseek(fd, position);
        }
        // BUG: This fd is the grate's fd, while the data pointer is from the 
        // target cage.  This means that 3i needs to be able to support a mix
        // of cage associations for different arguments...  BUG BUG BUG
        let amt_read = MAKE_SYSCALL(targetcage, READ_SYSID, fd, data, amount).unwrap();
        // do error handling, likely panic, since no error should occur...
    }
    return amt_read;  // Update virt_metadata position...
    
}



fn main() {
    // Setup my item table...
    init_item_table();

    // Have the virtual_fs initialize itself...
    virt_metadata.initialize_fs_metadata();

    // Register my calls
    let mycalls = virt_metadata::data_storage_interface {
        create_item: my_create_item,
        open_item: my_open_item,
        close_item: my_close_item,
        store_data: my_store_data,
        read_data: my_read_data,
        // could implement or add others...
        log_action:virt_metadata::DEFAULT,
        // persist metadata out into items.
        store_directories:true,
        store_inodes:true,
    };


    // need to replace calls with the right ones for our children
    virt_metadata.setup_interposition(mycalls);

    // Need to instantiate child cage(s) here...  
    lind_encasement.initialize_children_and_consume_thread();
    // Never reaches here!
}
