#[cfg(test)]
pub mod net_tests {
    use super::super::*;
    use crate::interface;
    use crate::safeposix::{cage::*, dispatcher::*, filesystem};
    use std::mem::size_of;
    use std::sync::{Arc, Barrier};

    use std::io::Write;
    use std::io;
    use std::ptr;
    use libc::*;
    use std::ffi::CString;
    use std::ffi::CStr;

    use std::net::SocketAddrV4;
    use std::net::Ipv4Addr;

    use crate::example_grates::fdtable::*;

    use libc::*;

    pub fn net_tests() {
        ut_lind_net_bind();
        // ut_lind_net_socketpair();
        ut_lind_net_connect();
        ut_lind_net_socket();
        ut_lind_net_epoll();
    }

    pub fn ut_lind_net_bind() {
        lindrustinit(0);
        let cage = interface::cagetable_getref(1);
        let sockfd = cage.socket_syscall(libc::AF_INET, libc::SOCK_STREAM, 0);

        let mut addr: sockaddr_in = unsafe { std::mem::zeroed() };
        addr.sin_family = libc::AF_INET as u16;
        addr.sin_addr.s_addr = INADDR_ANY;
        addr.sin_port = 8080_u16.to_be();//8080

        //first bind should work... but second bind should not
        assert_eq!(cage.bind_syscall(sockfd, &addr as *const _ as *const _, std::mem::size_of::<sockaddr_in>() as u32), 0);

        //trying to bind another to the same IP/PORT
        let sockfd2 = cage.socket_syscall(libc::AF_INET, libc::SOCK_STREAM, 0);
        assert_eq!(
            cage.bind_syscall(sockfd2, &addr as *const _ as *const _, std::mem::size_of::<sockaddr_in>() as u32),
            -1
        ); //already bound so should fail

        //UDP should still work...
        let sockfd3 = cage.socket_syscall(libc::AF_INET, libc::SOCK_DGRAM, 0);
        assert_eq!(cage.bind_syscall(sockfd3, &addr as *const _ as *const _, std::mem::size_of::<sockaddr_in>() as u32), 0);

        assert_eq!(cage.exit_syscall(libc::EXIT_SUCCESS), libc::EXIT_SUCCESS);
        lindrustfinalize();
    }

    
    pub fn ut_lind_net_socket() {
        lindrustinit(0);
        let cage = interface::cagetable_getref(1);

        let mut sockfd = cage.socket_syscall(libc::AF_INET, libc::SOCK_STREAM, 0);
        let sockfd2 = cage.socket_syscall(libc::AF_INET, libc::SOCK_STREAM, libc::IPPROTO_TCP);

        let sockfd3 = cage.socket_syscall(libc::AF_INET, libc::SOCK_DGRAM, 0);
        let sockfd4 = cage.socket_syscall(libc::AF_INET, libc::SOCK_DGRAM, libc::IPPROTO_UDP);

        //checking that the fd's are correct
        assert!(sockfd >= 0);
        assert!(sockfd2 >= 0);
        assert!(sockfd3 >= 0);
        assert!(sockfd4 >= 0);

        //let's check an illegal operation...
        let sockfddomain = cage.socket_syscall(libc::AF_UNIX, libc::SOCK_DGRAM, 0);
        assert!(sockfddomain > 0);

        sockfd = cage.socket_syscall(libc::AF_INET, libc::SOCK_STREAM, 0);
        assert!(sockfd > 0);

        assert_eq!(cage.close_syscall(sockfd), 0);
        assert_eq!(cage.exit_syscall(libc::EXIT_SUCCESS), libc::EXIT_SUCCESS);
        lindrustfinalize();
    }

    pub fn ut_lind_net_connect() {
        lindrustinit(0);
        let cage = interface::cagetable_getref(1);

        let server_fd = cage.socket_syscall(libc::AF_INET, libc::SOCK_STREAM, 0);
        assert!(server_fd > 0);
        let mut server_addr: libc::sockaddr_in = unsafe {
            std::mem::zeroed()
        };
        server_addr.sin_family = libc::AF_INET as u16;
        server_addr.sin_addr.s_addr = libc::INADDR_ANY;
        server_addr.sin_port = 7878_u16.to_be(); 

        let bind_result = cage.bind_syscall(
            server_fd,
            &server_addr as *const _ as *const _,
            std::mem::size_of::<libc::sockaddr_in>() as u32,
        );
        
        if bind_result < 0 {
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
        }

        let listen_result = cage.listen_syscall(server_fd, 128);
        if listen_result < 0 {
            panic!("listen_result");
        }

        cage.fork_syscall(2);

        let thread = interface::helper_thread(move || {
            // Client
            let cage2 = interface::cagetable_getref(2);
            let clientfd = cage2.socket_syscall(libc::AF_INET, libc::SOCK_STREAM, 0);
            if clientfd < 0 {
                panic!("Failed to create socket");
            }

            let connect_result = cage2.connect_syscall(
                clientfd,
                &server_addr as *const libc::sockaddr_in as *const libc::sockaddr,
                std::mem::size_of::<libc::sockaddr_in>() as u32,
            );
            if connect_result < 0 {
                panic!("Failed to connect to server");
            }
            let message = CString::new("Hello from client").unwrap();
            let sendret = cage2.send_syscall(clientfd, message.as_ptr() as *const u8, message.to_bytes().len(), 0);
            
            cage2.close_syscall(clientfd);
            assert_eq!(cage2.exit_syscall(libc::EXIT_SUCCESS), libc::EXIT_SUCCESS);
        });

        let mut client_addr: libc::sockaddr_in = unsafe {
            std::mem::zeroed()
        };
        let mut addr_len = std::mem::size_of::<libc::sockaddr_in>() as u32;
        let client_fd = cage.accept_syscall(
            server_fd,
            &mut client_addr as *mut libc::sockaddr_in as *mut libc::sockaddr,
            addr_len,
        );
        if client_fd < 0 {
            panic!("client_fd");
        }

        let mut buffer = [0u8; 1024];
        let len = cage.recv_syscall(client_fd, buffer.as_mut_ptr() as *mut u8, buffer.len(), 0);
        if len == 0 {
            panic!("Fail on child recv");
        }
        cage.close_syscall(client_fd);
        cage.close_syscall(server_fd);
        thread.join().unwrap();
        assert_eq!(cage.exit_syscall(libc::EXIT_SUCCESS), libc::EXIT_SUCCESS);
        lindrustfinalize();
    }

    pub fn ut_lind_net_socketpair() {
        lindrustinit(0);
        let cage = interface::cagetable_getref(1);
        let mut socketpair = interface::SockPair::default();
        cage.socketpair_syscall(libc::AF_UNIX, libc::SOCK_STREAM, 0, &mut socketpair);
        // assert_eq!(
        //     Cage::socketpair_syscall(&cage.clone(), libc::AF_UNIX, libc::SOCK_STREAM, 0, &mut socketpair),
        //     0
        // );
        let cage2 = cage.clone();

        let thread = interface::helper_thread(move || {
            let mut buf = sizecbuf(10);
            loop {
                let result = cage2.recv_syscall(socketpair.sock2, buf.as_mut_ptr(), 10, 0);
                if result != -libc::EINTR {
                    break; // if the error was EINTR, retry the syscall
                }
            }
            assert_eq!(cbuf2str(&buf), "test\0\0\0\0\0\0");

            interface::sleep(interface::RustDuration::from_millis(30));
            assert_eq!(
                cage2.send_syscall(socketpair.sock2, str2cbuf("Socketpair Test"), 15, 0),
                15
            );
        });

        assert_eq!(
            cage.send_syscall(socketpair.sock1, str2cbuf("test"), 4, 0),
            4
        );

        let mut buf2 = sizecbuf(15);
        loop {
            let result = cage.recv_syscall(socketpair.sock1, buf2.as_mut_ptr(), 15, 0);
            if result != -libc::EINTR {
                break; // if the error was EINTR, retry the syscall
            }
        }
        let str2 = cbuf2str(&buf2);
        assert_eq!(str2, "Socketpair Test");

        thread.join().unwrap();

        assert_eq!(cage.close_syscall(socketpair.sock1), 0);
        assert_eq!(cage.close_syscall(socketpair.sock2), 0);

        // end of the socket pair test (note we are only supporting AF_UNIX and TCP)

        assert_eq!(cage.exit_syscall(libc::EXIT_SUCCESS), libc::EXIT_SUCCESS);
        lindrustfinalize();
    }


    pub fn ut_lind_net_epoll() {
        lindrustinit(0);
        let cage = interface::cagetable_getref(1);

        let epoll_fd = cage.epoll_create_syscall(0);
        assert_ne!(epoll_fd, -1);

        let mut pipefds = PipeArray {
            readfd: 0,
            writefd: 0,
        };
        assert_eq!(cage.pipe_syscall(&mut pipefds), 0);

        assert_eq!(cage.fork_syscall(2), 0);
        let sender = std::thread::spawn(move || {
            let cage2 = interface::cagetable_getref(2);
            
            if cage2.close_syscall(pipefds.readfd) < 0 {
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
                println!("pipefds.readfd: {:?}", pipefds.readfd);
                io::stdout().flush().unwrap();
                panic!();
            }

            let message = b"Hello from child";
            
            if cage2.write_syscall(pipefds.writefd, message.as_ptr(), message.len()) < 0 {
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
                println!("pipefds.writefd: {:?}", pipefds.writefd);
                io::stdout().flush().unwrap();
                panic!();
            }
            assert_eq!(cage2.close_syscall(pipefds.writefd), 0);
            assert_eq!(cage2.exit_syscall(libc::EXIT_SUCCESS), libc::EXIT_SUCCESS);
        });

        assert_eq!(cage.close_syscall(pipefds.writefd), 0);
        // let mut epollevent = EpollEvent {
        //     events: libc::EPOLLIN as u32,
        //     fd: pipefds.readfd,
        // };

        // if cage.epoll_ctl_syscall(epoll_fd, libc::EPOLL_CTL_ADD, pipefds.readfd, &mut epollevent) < 0 {
        //     let err = unsafe {
        //         libc::__errno_location()
        //     };
        //     let err_str = unsafe {
        //         libc::strerror(*err)
        //     };
        //     let err_msg = unsafe {
        //         CStr::from_ptr(err_str).to_string_lossy().into_owned()
        //     };
        //     let kernelfd = translate_virtual_fd(1, pipefds.readfd).unwrap();
        //     println!("kernel fd: {:?}", kernelfd);
        //     println!("Error message: {:?}", err_msg);
        //     println!("pipefds.readfd: {:?}", pipefds.readfd);
        //     io::stdout().flush().unwrap();
        //     panic!();
        // }


        // let mut epoll_events = [EpollEvent{
        //     events: 0,
        //     fd: 0,
        // }; 10];
        // assert_ne!(cage.epoll_wait_syscall(epoll_fd, &epoll_events, epoll_events.len() as i32, -1), -1);
        let mut buffer = [0; 128];
        assert_ne!(cage.read_syscall(pipefds.readfd, buffer.as_mut_ptr(), buffer.len()), -1);

        assert_ne!(cage.close_syscall(pipefds.readfd), -1);
        // assert_ne!(cage.close_syscall(epoll_fd), -1);
        sender.join().unwrap();
        assert_eq!(cage.exit_syscall(libc::EXIT_SUCCESS), libc::EXIT_SUCCESS);
        lindrustfinalize();
    }
}
