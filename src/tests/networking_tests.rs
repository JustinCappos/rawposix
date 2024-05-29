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
        // ut_lind_net_bind();
        ut_lind_net_socketpair();
        // ut_lind_net_connect();
        // ut_lind_net_socket();
        // ut_lind_net_epoll();
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
        assert!(sockfd > 0);
        assert!(sockfd2 > 0);
        assert!(sockfd3 > 0);
        assert!(sockfd4 > 0);

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
        // assert!(bind_result > 0);
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

            let mut buffer = [0u8; 1024];
            let len = cage2.recv_syscall(clientfd, buffer.as_mut_ptr() as *mut u8, buffer.len(), 0);
            if len == 0 {
                panic!("Fail on child recv");
            }
            
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
        // interface::sleep(interface::RustDuration::from_millis(100));
        let message = CString::new("Hello from client").unwrap();
        let sendret = cage.send_syscall(client_fd, message.as_ptr() as *const u8, message.to_bytes().len(), 0);

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


    /* Creates an epoll instance, registers the server socket and file descriptor with epoll, and then wait for events using
    epoll_wait_syscall(). It handles the events based on their types (EPOLLIN or EPOLLOUT) and performs the necessary operations
    like accepting new connections, sending/receiving data, and modifying the event flags */
    pub fn ut_lind_net_epoll() {
        lindrustinit(0);
        let cage = interface::cagetable_getref(1);

        // let filefd = cage.open_syscall("/home/lind/lind_project/src/rawposix/tmp/netepolltest.txt", O_CREAT | O_EXCL | O_RDWR, (S_IRUSR | S_IWUSR | S_IXUSR | S_IRGRP | S_IWGRP | S_IXGRP | S_IROTH | S_IWOTH | S_IXOTH) as u32);
        // assert!(filefd > 0);
        // assert_eq!(filefd, 0);

        let serversockfd = cage.socket_syscall(libc::AF_INET, libc::SOCK_STREAM, 0);
        let clientsockfd1 = cage.socket_syscall(libc::AF_INET, libc::SOCK_STREAM, 0);
        let clientsockfd2 = cage.socket_syscall(libc::AF_INET, libc::SOCK_STREAM, 0);
        assert!(serversockfd > 0);
        assert!(clientsockfd1 > 0);
        assert!(clientsockfd2 > 0);

        // Create and set up the file descriptor and sockets
        // let port: u16 = 53019;
        let mut addr: sockaddr_in = unsafe {
            std::mem::zeroed()
        };
        addr.sin_family = libc::AF_INET as u16;
        addr.sin_addr.s_addr = INADDR_ANY;
        addr.sin_port = 8080_u16.to_be(); 

        assert_eq!(cage.bind_syscall(serversockfd, &addr as *const _ as *const _, std::mem::size_of::<sockaddr_in>() as u32), 0);
        assert_eq!(cage.listen_syscall(serversockfd, 4), 0);

        let mut event_list = vec![
            EpollEvent {
                events: libc::EPOLLIN as u32,
                fd: serversockfd,
            },
        ];

        cage.fork_syscall(2);
        // Client 1 connects to the server to send and recv data
        let thread1 = interface::helper_thread(move || {
            interface::sleep(interface::RustDuration::from_millis(30));
            let cage2 = interface::cagetable_getref(2);
            // Connect to server and send data
            // assert_eq!(cage2.connect_syscall(clientsockfd1, &addr as *const _ as *const _, std::mem::size_of::<sockaddr_in>() as u32), 0);
            if cage2.connect_syscall(clientsockfd1, &addr as *const _ as *const _, std::mem::size_of::<sockaddr_in>() as u32) < 0 {
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
            if cage2.send_syscall(clientsockfd1, str2cbuf(&"test"), 4, 0) != 4 {
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
                panic!("");
            }
            // Wait for data processing, give it a longer pause time so that it can process all of the data received
            interface::sleep(interface::RustDuration::from_millis(100));
            // Close the server socket and exit the thread
            assert_eq!(cage2.close_syscall(serversockfd), 0);
            cage2.exit_syscall(libc::EXIT_SUCCESS);
        });

        cage.fork_syscall(3);
        // Client 2 connects to the server to send and recv data
        let thread2 = interface::helper_thread(move || {
            interface::sleep(interface::RustDuration::from_millis(45));
            let cage3 = interface::cagetable_getref(3);
            // Connect to server and send data
            // assert_eq!(cage3.connect_syscall(clientsockfd2, &addr as *const _ as *const _, std::mem::size_of::<sockaddr_in>() as u32), 0);
            if cage3.connect_syscall(clientsockfd2, &addr as *const _ as *const _, std::mem::size_of::<sockaddr_in>() as u32) < 0 {
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
                panic!("2207");
            }
            assert_eq!(
                cage3.send_syscall(clientsockfd2, str2cbuf(&"test"), 4, 0),
                4
            );

            interface::sleep(interface::RustDuration::from_millis(100));
            // Close the server socket and exit the thread
            assert_eq!(cage3.close_syscall(serversockfd), 0);
            cage3.exit_syscall(libc::EXIT_SUCCESS);
        });

        // Acting as the server and processing the request
        let thread3 = interface::helper_thread(move || {
            let epfd = cage.epoll_create_syscall(1);
            assert!(epfd > 0);

            assert_eq!(
                cage.epoll_ctl_syscall(epfd, libc::EPOLL_CTL_ADD, serversockfd, &mut event_list[0]),
                0
            );
            // assert_eq!(
            //     cage.epoll_ctl_syscall(epfd, libc::EPOLL_CTL_ADD, filefd, &mut event_list[1]),
            //     0
            // );
            // if cage.epoll_ctl_syscall(epfd, libc::EPOLL_CTL_ADD, filefd, &mut event_list[1]) < 0 {
            //     let err = unsafe {
            //         libc::__errno_location()
            //     };
            //     let err_str = unsafe {
            //         libc::strerror(*err)
            //     };
            //     let err_msg = unsafe {
            //         CStr::from_ptr(err_str).to_string_lossy().into_owned()
            //     };
            //     println!("errno: {:?}", err);
            //     println!("Error message: {:?}", err_msg);
            //     println!("filefd: {:?}", filefd);
            //     println!("FDtable: {:?}", GLOBALFDTABLE);
            //     io::stdout().flush().unwrap();
            //     panic!("2207");
            // }

            // Event processing loop
            for _counter in 0..600 {
                let num_events = cage.epoll_wait_syscall(
                    epfd,
                    &mut event_list,
                    1,
                    0,
                );
                assert!(num_events >= 0);

                // Wait for events using epoll_wait_syscall
                for event in &mut event_list[..num_events as usize] {
                    // Check for any activity in the input socket and if there are events ready for reading
                    if event.events & (libc::EPOLLIN as u32) != 0 {
                        // If the socket returned was listener socket, then there's a new connection
                        if event.fd == serversockfd {
                            // Handle new connections
                            let client_ip = Ipv4Addr::new(127, 0, 0, 1);
                            let client_socket_addr = SocketAddrV4::new(client_ip, 7878);
                            let mut client_addr: libc::sockaddr_in = unsafe {
                                std::mem::zeroed()
                            };
                            client_addr.sin_family = libc::AF_INET as u16;
                            client_addr.sin_addr.s_addr = u32::from(client_ip).to_be();
                            client_addr.sin_port = 8080_u16.to_be(); 

                            let client_len = std::mem::size_of::<sockaddr_in>() as u32;
                            let newsockfd = cage.accept_syscall(
                                serversockfd,
                                &mut client_addr as *mut _ as *mut _,
                                client_len,
                            );
                            let event = interface::EpollEvent {
                                events: libc::EPOLLIN as u32,
                                fd: newsockfd,
                            };
                            // Error raised to indicate that the socket file descriptor couldn't be added to the epoll instance
                            assert_eq!(
                                cage.epoll_ctl_syscall(epfd, libc::EPOLL_CTL_ADD, newsockfd, &event),
                                0
                            );
                        } else {
                            // Handle receiving data from established connections
                            let mut buf = sizecbuf(4);
                            let recres = cage.recv_syscall(event.fd, buf.as_mut_ptr(), 4, 0);
                            assert_eq!(recres & !4, 0);
                            if recres == 4 {
                                assert_eq!(cbuf2str(&buf), "test");
                                event.events = libc::EPOLLOUT as u32;
                            } else {
                                assert_eq!(cage.close_syscall(event.fd), 0);
                            }
                        }
                    }

                    if event.events & (libc::EPOLLOUT as u32) != 0 {
                        // Handle sending data over connections
                        assert_eq!(cage.send_syscall(event.fd, str2cbuf(&"test"), 4, 0), 4);
                        event.events = libc::EPOLLIN as u32;
                    }
                }
            }

            // Close the server socket and exit the thread
            assert_eq!(cage.close_syscall(serversockfd), 0);
            assert_eq!(cage.exit_syscall(libc::EXIT_SUCCESS), libc::EXIT_SUCCESS);
        });

        thread1.join().unwrap();
        thread2.join().unwrap();
        thread3.join().unwrap();

        lindrustfinalize();
    }
}
