// Copyright 2015 The Rust Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::io::IoSlice;
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::net::Shutdown;

use std::os::wasi::io::{AsFd, AsRawFd, BorrowedFd, FromRawFd, IntoRawFd, OwnedFd};

use std::time::{Duration, Instant};
use std::{io, slice};

use crate::{Domain, Protocol, SockAddr, Type};
use crate::{RecvFlags, TcpKeepalive};

pub(crate) use libc::c_int;

use wasmedge_wasi_socket::socket::Socket as WasmSocket;

// Used in `Domain`.
pub(crate) const AF_UNSPEC: c_int = wasmedge_wasi_socket::socket::AddressFamily::Unspec as c_int;
pub(crate) const AF_INET: c_int = wasmedge_wasi_socket::socket::AddressFamily::Inet4 as c_int;
pub(crate) const AF_INET6: c_int = wasmedge_wasi_socket::socket::AddressFamily::Inet6 as c_int;
// Used in `Type`.
pub(crate) const SOCK_STREAM: c_int = wasmedge_wasi_socket::socket::SocketType::Stream as c_int;
pub(crate) const SOCK_DGRAM: c_int = wasmedge_wasi_socket::socket::SocketType::Datagram as c_int;
// Used in `Protocol`.
pub(crate) const IPPROTO_TCP: c_int = wasmedge_wasi_socket::socket::AiProtocol::IPProtoTCP as c_int;
pub(crate) const IPPROTO_UDP: c_int = wasmedge_wasi_socket::socket::AiProtocol::IPProtoUDP as c_int;
// Used in `SockAddr`.

// Used in `Socket`.
pub(crate) const MSG_PEEK: c_int = 1 as c_int; // __WASI_RIFLAGS_RECV_PEEK
#[allow(unused)]
pub(crate) const MSG_WAITALL: c_int = 2 as c_int; // __WASI_RIFLAGS_RECV_WAITALL
pub(crate) const MSG_TRUNC: c_int = 1 as c_int; // __WASI_RIFLAGS_RECV_WAITALL

pub(crate) const SOL_SOCKET: c_int =
    wasmedge_wasi_socket::socket::SocketOptLevel::SolSocket as c_int;

pub(crate) const SO_REUSEADDR: c_int =
    wasmedge_wasi_socket::socket::SocketOptName::SoReuseaddr as c_int;
#[allow(unused)]
pub(crate) const SO_TYPE: c_int = wasmedge_wasi_socket::socket::SocketOptName::SoType as c_int;
#[allow(unused)]
pub(crate) const SO_ERROR: c_int = wasmedge_wasi_socket::socket::SocketOptName::SoError as c_int;
pub(crate) const SO_BROADCAST: c_int =
    wasmedge_wasi_socket::socket::SocketOptName::SoBroadcast as c_int;
pub(crate) const SO_RCVBUF: c_int = wasmedge_wasi_socket::socket::SocketOptName::SoRcvbuf as c_int;
pub(crate) const SO_RCVTIMEO: c_int =
    wasmedge_wasi_socket::socket::SocketOptName::SoRcvtimeo as c_int;
pub(crate) const SO_SNDBUF: c_int = wasmedge_wasi_socket::socket::SocketOptName::SoSndbuf as c_int;
pub(crate) const SO_SNDTIMEO: c_int =
    wasmedge_wasi_socket::socket::SocketOptName::SoSndtimeo as c_int;
pub(crate) const SO_KEEPALIVE: c_int =
    wasmedge_wasi_socket::socket::SocketOptName::SoKeepalive as c_int;

#[allow(unused)]
pub(crate) const SO_OOBINLINE: c_int =
    wasmedge_wasi_socket::socket::SocketOptName::SoOobinline as c_int;
#[allow(unused)]
pub(crate) const SO_LINGER: c_int = wasmedge_wasi_socket::socket::SocketOptName::SoLinger as c_int;
#[allow(unused)]
pub(crate) const SO_ACCEPTCONN: c_int =
    wasmedge_wasi_socket::socket::SocketOptName::SoAcceptconn as c_int;
#[allow(unused)]
pub(crate) const SO_BINDTODEVICE: c_int =
    wasmedge_wasi_socket::socket::SocketOptName::SoBindToDevice as c_int;

/// Helper macro to execute a system call that returns an `io::Result`.
macro_rules! syscall {
    ($fn: ident ( $($arg: expr),* $(,)* ) ) => {{
        #[allow(unused_unsafe)]
        let res = unsafe { libc::$fn($($arg, )*) };
        if res == -1 {
            Err(std::io::Error::last_os_error())
        } else {
            Ok(res)
        }
    }};
}

impl_debug!(Domain, self::AF_INET, self::AF_INET6, self::AF_UNSPEC);

/// Unix only API.
impl Type {
    /// Set `SOCK_NONBLOCK` on the `Type`.
    #[cfg(feature = "all")]
    #[cfg_attr(docsrs, doc(cfg(feature = "all")))]
    pub const fn nonblocking(self) -> Type {
        Type(self.0 | libc::O_NONBLOCK)
    }
}
impl_debug!(Type, self::SOCK_STREAM, self::SOCK_DGRAM,);

impl_debug!(Protocol, self::IPPROTO_TCP, self::IPPROTO_UDP,);

impl std::fmt::Debug for RecvFlags {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = f.debug_struct("RecvFlags");
        s.field("is_truncated", &self.is_truncated());
        s.finish()
    }
}

#[repr(transparent)]
pub struct MaybeUninitSlice<'a> {
    vec: libc::iovec,
    _lifetime: PhantomData<&'a mut [MaybeUninit<u8>]>,
}

unsafe impl<'a> Send for MaybeUninitSlice<'a> {}

unsafe impl<'a> Sync for MaybeUninitSlice<'a> {}

impl<'a> MaybeUninitSlice<'a> {
    pub(crate) fn new(buf: &'a mut [MaybeUninit<u8>]) -> MaybeUninitSlice<'a> {
        MaybeUninitSlice {
            vec: libc::iovec {
                iov_base: buf.as_mut_ptr().cast(),
                iov_len: buf.len(),
            },
            _lifetime: PhantomData,
        }
    }

    pub(crate) fn as_slice(&self) -> &[MaybeUninit<u8>] {
        unsafe { slice::from_raw_parts(self.vec.iov_base.cast(), self.vec.iov_len) }
    }

    pub(crate) fn as_mut_slice(&mut self) -> &mut [MaybeUninit<u8>] {
        unsafe { slice::from_raw_parts_mut(self.vec.iov_base.cast(), self.vec.iov_len) }
    }
}

// Used in `MsgHdr`.

pub(crate) type Socket = std::os::fd::RawFd;

pub(crate) unsafe fn socket_from_raw(socket: Socket) -> crate::socket::Inner {
    crate::socket::Inner::from_raw_fd(socket.as_raw_fd())
}

pub(crate) fn socket_as_raw(socket: &crate::socket::Inner) -> Socket {
    unsafe { Socket::from_raw_fd(socket.as_raw_fd()) }
}

pub(crate) fn socket_into_raw(socket: crate::socket::Inner) -> Socket {
    unsafe { Socket::from_raw_fd(socket.into_raw_fd()) }
}

pub(crate) fn socket(family: c_int, ty: c_int, _protocol: c_int) -> io::Result<Socket> {
    let addr_family = match family {
        self::AF_UNSPEC => wasmedge_wasi_socket::socket::AddressFamily::Unspec,
        self::AF_INET => wasmedge_wasi_socket::socket::AddressFamily::Inet4,
        self::AF_INET6 => wasmedge_wasi_socket::socket::AddressFamily::Inet6,
        _ => return Err(io::Error::from_raw_os_error(libc::EINVAL)),
    };
    let sock_kind = match ty {
        self::SOCK_DGRAM => wasmedge_wasi_socket::socket::SocketType::Datagram,
        self::SOCK_STREAM => wasmedge_wasi_socket::socket::SocketType::Stream,
        _ => return Err(io::Error::from_raw_os_error(libc::EINVAL)),
    };
    wasmedge_wasi_socket::socket::Socket::new(addr_family, sock_kind).map(|s| s.into_raw_fd())
}

pub(crate) fn bind(fd: Socket, addr: &SockAddr) -> io::Result<()> {
    let fd: &WasmSocket = unsafe { std::mem::transmute(&fd) };
    fd.bind(addr)
}

pub(crate) fn connect(fd: Socket, addr: &SockAddr) -> io::Result<()> {
    let fd: &WasmSocket = unsafe { std::mem::transmute(&fd) };
    fd.connect(addr)
}

pub(crate) fn poll_connect(socket: &crate::Socket, timeout: Duration) -> io::Result<()> {
    let start = Instant::now();

    let mut pollfd = libc::pollfd {
        fd: socket.as_raw_fd(),
        events: libc::POLLIN | libc::POLLOUT,
        revents: 0,
    };

    loop {
        let elapsed = start.elapsed();
        if elapsed >= timeout {
            return Err(io::ErrorKind::TimedOut.into());
        }

        let timeout = (timeout - elapsed).as_millis();
        let timeout = timeout.clamp(1, c_int::MAX as u128) as c_int;

        match syscall!(poll(&mut pollfd, 1, timeout)) {
            Ok(0) => return Err(io::ErrorKind::TimedOut.into()),
            Ok(_) => {
                // Error or hang up indicates an error (or failure to connect).
                if (pollfd.revents & libc::POLLHUP) != 0 || (pollfd.revents & libc::POLLERR) != 0 {
                    match socket.take_error() {
                        Ok(Some(err)) | Err(err) => return Err(err),
                        Ok(None) => {
                            return Err(io::Error::new(
                                io::ErrorKind::Other,
                                "no error set after POLLHUP",
                            ))
                        }
                    }
                }
                return Ok(());
            }
            // Got interrupted, try again.
            Err(ref err) if err.kind() == io::ErrorKind::Interrupted => continue,
            Err(err) => return Err(err),
        }
    }
}

pub(crate) fn listen(fd: Socket, backlog: c_int) -> io::Result<()> {
    let fd: &WasmSocket = unsafe { std::mem::transmute(&fd) };
    fd.listen(backlog)
}

pub(crate) fn accept(fd: Socket) -> io::Result<(Socket, SockAddr)> {
    let fd: &WasmSocket = unsafe { std::mem::transmute(&fd) };
    let s = fd.accept(false)?;
    let peer = s.get_peer()?;
    Ok((s.into_raw_fd(), peer))
}

pub(crate) fn getsockname(fd: Socket) -> io::Result<SockAddr> {
    let fd: &WasmSocket = unsafe { std::mem::transmute(&fd) };
    fd.get_local()
}

pub(crate) fn getpeername(fd: Socket) -> io::Result<SockAddr> {
    let fd: &WasmSocket = unsafe { std::mem::transmute(&fd) };
    fd.get_peer()
}

#[cfg(feature = "all")]
pub(crate) fn nonblocking(fd: Socket) -> io::Result<bool> {
    let fd: &WasmSocket = unsafe { std::mem::transmute(&fd) };
    fd.nonblocking()
}

pub(crate) fn set_nonblocking(fd: Socket, nonblocking: bool) -> io::Result<()> {
    let fd: &WasmSocket = unsafe { std::mem::transmute(&fd) };
    fd.set_nonblocking(nonblocking)
}

pub(crate) fn shutdown(fd: Socket, how: Shutdown) -> io::Result<()> {
    let fd: &WasmSocket = unsafe { std::mem::transmute(&fd) };
    fd.shutdown(how)
}

pub(crate) fn recv(fd: Socket, buf: &mut [MaybeUninit<u8>], flags: c_int) -> io::Result<usize> {
    let fd: &WasmSocket = unsafe { std::mem::transmute(&fd) };
    let (n, _) = fd.recv_with_flags(buf, flags as u16)?;
    Ok(n)
}

pub(crate) fn recv_from(
    fd: Socket,
    buf: &mut [MaybeUninit<u8>],
    flags: c_int,
) -> io::Result<(usize, SockAddr)> {
    let fd: &WasmSocket = unsafe { std::mem::transmute(&fd) };
    let (n, addr, _) = fd.recv_from_with_flags(buf, flags as u16)?;
    Ok((n, addr))
}

pub(crate) fn peek_sender(fd: Socket) -> io::Result<SockAddr> {
    // Unix-like platforms simply truncate the returned data, so this implementation is trivial.
    // However, for Windows this requires suppressing the `WSAEMSGSIZE` error,
    // so that requires a different approach.
    // NOTE: macOS does not populate `sockaddr` if you pass a zero-sized buffer.
    let (_, sender) = recv_from(fd, &mut [MaybeUninit::uninit(); 8], MSG_PEEK)?;
    Ok(sender)
}

pub(crate) fn recv_vectored(
    fd: Socket,
    bufs: &mut [crate::MaybeUninitSlice<'_>],
    flags: c_int,
) -> io::Result<(usize, RecvFlags)> {
    let fd: &WasmSocket = unsafe { std::mem::transmute(&fd) };

    let mut read_bufs: Vec<wasmedge_wasi_socket::socket::IovecRead> =
        bufs.iter_mut().map(|b| b.0.vec.into()).collect();

    let (n, flags) = fd.recv_vectored(&mut read_bufs, flags as u16)?;
    Ok((n, RecvFlags(flags as i32)))
}

pub(crate) fn recv_from_vectored(
    fd: Socket,
    bufs: &mut [crate::MaybeUninitSlice<'_>],
    flags: c_int,
) -> io::Result<(usize, RecvFlags, SockAddr)> {
    let fd: &WasmSocket = unsafe { std::mem::transmute(&fd) };

    let mut read_bufs: Vec<wasmedge_wasi_socket::socket::IovecRead> =
        bufs.iter_mut().map(|b| b.0.vec.into()).collect();

    let (n, addr, flags) = fd.recv_from_vectored(&mut read_bufs, flags as u16)?;
    Ok((n, RecvFlags(flags as i32), addr))
}

pub(crate) fn send(fd: Socket, buf: &[u8], _flags: c_int) -> io::Result<usize> {
    let fd: &WasmSocket = unsafe { std::mem::transmute(&fd) };
    fd.send(buf)
}

pub(crate) fn send_vectored(fd: Socket, bufs: &[IoSlice<'_>], flags: c_int) -> io::Result<usize> {
    let fd: &WasmSocket = unsafe { std::mem::transmute(&fd) };
    fd.send_vectored(bufs, flags as u16)
}

pub(crate) fn send_to(fd: Socket, buf: &[u8], addr: &SockAddr, _flags: c_int) -> io::Result<usize> {
    let fd: &WasmSocket = unsafe { std::mem::transmute(&fd) };
    fd.send_to(buf, addr.clone())
}

pub(crate) fn send_to_vectored(
    fd: Socket,
    bufs: &[IoSlice<'_>],
    addr: &SockAddr,
    flags: c_int,
) -> io::Result<usize> {
    let fd: &WasmSocket = unsafe { std::mem::transmute(&fd) };
    fd.send_to_vectored(bufs, addr.clone(), flags as u16)
}

/// Wrapper around `getsockopt` to deal with platform specific timeouts.
pub(crate) fn timeout_opt(fd: Socket, opt: c_int, val: c_int) -> io::Result<Option<Duration>> {
    let fd: &WasmSocket = unsafe { std::mem::transmute(&fd) };
    match (opt, val) {
        (self::SOL_SOCKET, self::SO_SNDTIMEO) => fd.get_send_timeout(),
        (self::SOL_SOCKET, self::SO_RCVTIMEO) => fd.get_recv_timeout(),
        _ => return Err(io::Error::from_raw_os_error(libc::EINVAL)),
    }
}

/// Wrapper around `setsockopt` to deal with platform specific timeouts.
pub(crate) fn set_timeout_opt(
    fd: Socket,
    opt: c_int,
    val: c_int,
    duration: Option<Duration>,
) -> io::Result<()> {
    let fd: &WasmSocket = unsafe { std::mem::transmute(&fd) };
    match (opt, val) {
        (self::SOL_SOCKET, self::SO_SNDTIMEO) => fd.set_send_timeout(duration),
        (self::SOL_SOCKET, self::SO_RCVTIMEO) => fd.set_recv_timeout(duration),
        _ => return Err(io::Error::from_raw_os_error(libc::EINVAL)),
    }
}

#[allow(unused_variables, unused)]
#[cfg(feature = "all")]
#[cfg_attr(docsrs, doc(cfg(feature = "all",)))]
pub(crate) fn keepalive_time(_fd: Socket) -> io::Result<Duration> {
    Err(std::io::Error::new(
        std::io::ErrorKind::Unsupported,
        "operation not supported on this platform",
    ))
}

#[allow(unused_variables, unused)]
pub(crate) fn set_tcp_keepalive(fd: Socket, keepalive: &TcpKeepalive) -> io::Result<()> {
    Err(std::io::Error::new(
        std::io::ErrorKind::Unsupported,
        "operation not supported on this platform",
    ))
}

/// Caller must ensure `T` is the correct type for `opt` and `val`.
pub(crate) unsafe fn setsockopt<T>(
    fd: Socket,
    opt: c_int,
    val: c_int,
    payload: T,
) -> io::Result<()> {
    let fd: &WasmSocket = unsafe { std::mem::transmute(&fd) };
    fd.setsockopt(opt.try_into()?, val.try_into()?, payload)
}

/// Unix only API.
impl crate::Socket {
    /// Returns `true` if `listen(2)` was called on this socket by checking the
    /// `SO_ACCEPTCONN` option on this socket.
    #[cfg(feature = "all")]
    #[cfg_attr(docsrs, doc(cfg(feature = "all")))]
    pub fn is_listener(&self) -> io::Result<bool> {
        let fd = self.as_raw();
        let fd: &WasmSocket = unsafe { std::mem::transmute(&fd) };
        fd.is_listener()
    }

    /// Gets the value for the `SO_BINDTODEVICE` option on this socket.
    ///
    /// This value gets the socket binded device's interface name.
    #[cfg(feature = "all")]
    #[cfg_attr(docsrs, doc(cfg(feature = "all")))]
    pub fn device(&self) -> io::Result<Option<Vec<u8>>> {
        let fd = self.as_raw();
        let fd: &WasmSocket = unsafe { std::mem::transmute(&fd) };
        fd.device()
    }
}

/// Socket options get/set;
///
/// Additional documentation can be found in documentation of the OS.
/// * Linux: <https://man7.org/linux/man-pages/man7/socket.7.html>
/// * Windows: <https://docs.microsoft.com/en-us/windows/win32/winsock/sol-socket-socket-options>
impl crate::Socket {
    /// Returns the [`Type`] of this socket by checking the `SO_TYPE` option on
    /// this socket.
    pub fn r#type(&self) -> io::Result<Type> {
        let fd = self.as_raw();
        let s: &WasmSocket = unsafe { std::mem::transmute(&fd) };
        s.r#type().map(|t| match t {
            wasmedge_wasi_socket::socket::SocketType::Datagram => Type::DGRAM,
            wasmedge_wasi_socket::socket::SocketType::Stream => Type::STREAM,
            _ => unreachable!(),
        })
    }

    /// Get the value of the `SO_BROADCAST` option for this socket.
    ///
    /// For more information about this option, see [`set_broadcast`].
    ///
    /// [`set_broadcast`]: Socket::set_broadcast
    pub fn broadcast(&self) -> io::Result<bool> {
        let fd = self.as_raw();
        let s: &WasmSocket = unsafe { std::mem::transmute(&fd) };
        s.broadcast()
    }

    /// Set the value of the `SO_BROADCAST` option for this socket.
    ///
    /// When enabled, this socket is allowed to send packets to a broadcast
    /// address.
    pub fn set_broadcast(&self, broadcast: bool) -> io::Result<()> {
        unsafe { setsockopt(self.as_raw(), SOL_SOCKET, SO_BROADCAST, broadcast as c_int) }
    }

    /// Get the value of the `SO_ERROR` option on this socket.
    ///
    /// This will retrieve the stored error in the underlying socket, clearing
    /// the field in the process. This can be useful for checking errors between
    /// calls.
    pub fn take_error(&self) -> io::Result<Option<io::Error>> {
        let fd = self.as_raw();
        let s: &WasmSocket = unsafe { std::mem::transmute(&fd) };
        if let Err(e) = s.take_error() {
            Ok(Some(e))
        } else {
            Ok(None)
        }
    }

    /// Get the value of the `SO_KEEPALIVE` option on this socket.
    ///
    /// For more information about this option, see [`set_keepalive`].
    ///
    /// [`set_keepalive`]: Socket::set_keepalive
    pub fn keepalive(&self) -> io::Result<bool> {
        let fd = self.as_raw();
        let s: &WasmSocket = unsafe { std::mem::transmute(&fd) };
        s.keepalive()
    }

    /// Set value for the `SO_KEEPALIVE` option on this socket.
    ///
    /// Enable sending of keep-alive messages on connection-oriented sockets.
    pub fn set_keepalive(&self, keepalive: bool) -> io::Result<()> {
        unsafe { setsockopt(self.as_raw(), SOL_SOCKET, SO_KEEPALIVE, keepalive as c_int) }
    }

    /// Get the value of the `SO_LINGER` option on this socket.
    ///
    /// For more information about this option, see [`set_linger`].
    ///
    /// [`set_linger`]: Socket::set_linger

    pub fn linger(&self) -> io::Result<Option<Duration>> {
        Err(std::io::Error::new(
            std::io::ErrorKind::Unsupported,
            "operation not supported on this platform",
        ))
    }

    /// Set value for the `SO_LINGER` option on this socket.
    ///
    /// If `linger` is not `None`, a close(2) or shutdown(2) will not return
    /// until all queued messages for the socket have been successfully sent or
    /// the linger timeout has been reached. Otherwise, the call returns
    /// immediately and the closing is done in the background. When the socket
    /// is closed as part of exit(2), it always lingers in the background.
    ///
    /// # Notes
    ///
    /// On most OSs the duration only has a precision of seconds and will be
    /// silently truncated.
    ///
    /// On Apple platforms (e.g. macOS, iOS, etc) this uses `SO_LINGER_SEC`.
    pub fn set_linger(&self, _linger: Option<Duration>) -> io::Result<()> {
        Err(std::io::Error::new(
            std::io::ErrorKind::Unsupported,
            "operation not supported on this platform",
        ))
    }

    /// Get value for the `SO_OOBINLINE` option on this socket.
    ///
    /// For more information about this option, see [`set_out_of_band_inline`].
    ///
    /// [`set_out_of_band_inline`]: Socket::set_out_of_band_inline
    #[cfg(not(any(target_os = "redox")))]
    #[cfg_attr(docsrs, doc(cfg(not(any(target_os = "redox")))))]
    pub fn out_of_band_inline(&self) -> io::Result<bool> {
        Err(std::io::Error::new(
            std::io::ErrorKind::Unsupported,
            "operation not supported on this platform",
        ))
    }

    /// Set value for the `SO_OOBINLINE` option on this socket.
    ///
    /// If this option is enabled, out-of-band data is directly placed into the
    /// receive data stream. Otherwise, out-of-band data is passed only when the
    /// `MSG_OOB` flag is set during receiving. As per RFC6093, TCP sockets
    /// using the Urgent mechanism are encouraged to set this flag.
    #[cfg(not(any(target_os = "redox")))]
    #[cfg_attr(docsrs, doc(cfg(not(any(target_os = "redox")))))]
    pub fn set_out_of_band_inline(&self, _oob_inline: bool) -> io::Result<()> {
        Err(std::io::Error::new(
            std::io::ErrorKind::Unsupported,
            "operation not supported on this platform",
        ))
    }

    /// Get value for the `SO_RCVBUF` option on this socket.
    ///
    /// For more information about this option, see [`set_recv_buffer_size`].
    ///
    /// [`set_recv_buffer_size`]: Socket::set_recv_buffer_size
    pub fn recv_buffer_size(&self) -> io::Result<usize> {
        let fd = self.as_raw();
        let s: &WasmSocket = unsafe { std::mem::transmute(&fd) };
        s.recv_buffer_size()
    }

    /// Set value for the `SO_RCVBUF` option on this socket.
    ///
    /// Changes the size of the operating system's receive buffer associated
    /// with the socket.
    pub fn set_recv_buffer_size(&self, size: usize) -> io::Result<()> {
        unsafe { setsockopt(self.as_raw(), SOL_SOCKET, SO_RCVBUF, size as c_int) }
    }

    /// Get value for the `SO_RCVTIMEO` option on this socket.
    ///
    /// If the returned timeout is `None`, then `read` and `recv` calls will
    /// block indefinitely.
    pub fn read_timeout(&self) -> io::Result<Option<Duration>> {
        timeout_opt(self.as_raw(), SOL_SOCKET, SO_RCVTIMEO)
    }

    /// Set value for the `SO_RCVTIMEO` option on this socket.
    ///
    /// If `timeout` is `None`, then `read` and `recv` calls will block
    /// indefinitely.
    pub fn set_read_timeout(&self, duration: Option<Duration>) -> io::Result<()> {
        set_timeout_opt(self.as_raw(), SOL_SOCKET, SO_RCVTIMEO, duration)
    }

    /// Get the value of the `SO_REUSEADDR` option on this socket.
    ///
    /// For more information about this option, see [`set_reuse_address`].
    ///
    /// [`set_reuse_address`]: Socket::set_reuse_address
    pub fn reuse_address(&self) -> io::Result<bool> {
        let fd = self.as_raw();
        let s: &WasmSocket = unsafe { std::mem::transmute(&fd) };
        s.reuse_address()
    }

    /// Set value for the `SO_REUSEADDR` option on this socket.
    ///
    /// This indicates that futher calls to `bind` may allow reuse of local
    /// addresses. For IPv4 sockets this means that a socket may bind even when
    /// there's a socket already listening on this port.
    pub fn set_reuse_address(&self, reuse: bool) -> io::Result<()> {
        unsafe { setsockopt(self.as_raw(), SOL_SOCKET, SO_REUSEADDR, reuse as c_int) }
    }

    /// Get the value of the `SO_SNDBUF` option on this socket.
    ///
    /// For more information about this option, see [`set_send_buffer_size`].
    ///
    /// [`set_send_buffer_size`]: Socket::set_send_buffer_size
    pub fn send_buffer_size(&self) -> io::Result<usize> {
        let fd = self.as_raw();
        let s: &WasmSocket = unsafe { std::mem::transmute(&fd) };
        s.send_buffer_size()
    }

    /// Set value for the `SO_SNDBUF` option on this socket.
    ///
    /// Changes the size of the operating system's send buffer associated with
    /// the socket.
    pub fn set_send_buffer_size(&self, size: usize) -> io::Result<()> {
        unsafe { setsockopt(self.as_raw(), SOL_SOCKET, SO_SNDBUF, size as c_int) }
    }

    /// Get value for the `SO_SNDTIMEO` option on this socket.
    ///
    /// If the returned timeout is `None`, then `write` and `send` calls will
    /// block indefinitely.
    pub fn write_timeout(&self) -> io::Result<Option<Duration>> {
        timeout_opt(self.as_raw(), SOL_SOCKET, SO_SNDTIMEO)
    }

    /// Set value for the `SO_SNDTIMEO` option on this socket.
    ///
    /// If `timeout` is `None`, then `write` and `send` calls will block
    /// indefinitely.
    pub fn set_write_timeout(&self, duration: Option<Duration>) -> io::Result<()> {
        set_timeout_opt(self.as_raw(), SOL_SOCKET, SO_SNDTIMEO, duration)
    }
}

#[cfg_attr(docsrs, doc(cfg(unix)))]
impl AsFd for crate::Socket {
    fn as_fd(&self) -> BorrowedFd<'_> {
        // SAFETY: lifetime is bound by self.
        unsafe { BorrowedFd::borrow_raw(self.as_raw_fd()) }
    }
}

#[cfg_attr(docsrs, doc(cfg(unix)))]
impl AsRawFd for crate::Socket {
    fn as_raw_fd(&self) -> c_int {
        self.as_raw().as_raw_fd()
    }
}

#[cfg_attr(docsrs, doc(cfg(unix)))]
impl From<crate::Socket> for OwnedFd {
    fn from(sock: crate::Socket) -> OwnedFd {
        // SAFETY: sock.into_raw() always returns a valid fd.
        unsafe { OwnedFd::from_raw_fd(sock.into_raw().into_raw_fd()) }
    }
}

#[cfg_attr(docsrs, doc(cfg(unix)))]
impl IntoRawFd for crate::Socket {
    fn into_raw_fd(self) -> c_int {
        self.into_raw().into_raw_fd()
    }
}

#[cfg_attr(docsrs, doc(cfg(unix)))]
impl From<OwnedFd> for crate::Socket {
    fn from(fd: OwnedFd) -> crate::Socket {
        // SAFETY: `OwnedFd` ensures the fd is valid.
        unsafe { crate::Socket::from_raw_fd(fd.into_raw_fd()) }
    }
}

#[cfg_attr(docsrs, doc(cfg(unix)))]
impl FromRawFd for crate::Socket {
    unsafe fn from_raw_fd(fd: c_int) -> crate::Socket {
        crate::Socket::from_raw(self::Socket::from_raw_fd(fd))
    }
}
