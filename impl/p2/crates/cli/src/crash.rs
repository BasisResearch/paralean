//! Process lifecycle for the CLI: FDB network teardown and opt-in native-crash reports.
//!
//! The FDB client library's network thread must be stopped and joined before the process
//! exits (FDB C API: exiting while `fdb_run_network` runs is undefined behaviour). `Teardown`
//! does that when `main` returns *or unwinds*, after the Tokio runtime (and every task, FDB
//! database and future it owns) has been dropped.
//!
//! `PARALEAN_SEGV_REPORT=1` installs a SIGSEGV/SIGBUS handler that writes one line (signal,
//! `si_code`, fault address, instruction pointer, thread ID and name, lifecycle stage) and
//! `/proc/self/maps` to stderr using only async-signal-safe calls, then restores the
//! previous action. A hardware fault then re-executes under it (Rust's stack-overflow
//! handler or the default action, which dumps a core when `ulimit -c` allows). Unset, the
//! process's signal handling is unchanged.

use std::sync::atomic::{AtomicU8, Ordering};

/// Where the process is in its lifecycle, reported by the crash handler.
#[derive(Clone, Copy)]
#[repr(u8)]
pub enum Stage {
    Run = 0,
    RuntimeDropped = 1,
    FdbStopping = 2,
    FdbStopped = 3,
}

static STAGE: AtomicU8 = AtomicU8::new(Stage::Run as u8);

pub fn stage(s: Stage) {
    STAGE.store(s as u8, Ordering::SeqCst);
}

/// Stops and joins the FDB network thread on drop (normal return or unwinding).
pub struct Teardown;

impl Drop for Teardown {
    fn drop(&mut self) {
        stage(Stage::FdbStopping);
        paralean_store::meta::shutdown();
        stage(Stage::FdbStopped);
    }
}

#[cfg(target_os = "linux")]
mod imp {
    use super::STAGE;
    use std::mem::MaybeUninit;
    use std::sync::atomic::Ordering;

    const SIGNALS: [libc::c_int; 2] = [libc::SIGSEGV, libc::SIGBUS];
    static mut PREVIOUS: [MaybeUninit<libc::sigaction>; 2] = [MaybeUninit::uninit(), MaybeUninit::uninit()];

    /// Fixed-capacity formatter that never allocates.
    struct Line {
        buf: [u8; 512],
        len: usize,
    }
    impl Line {
        fn bytes(&mut self, b: &[u8]) {
            for &c in b {
                if self.len < self.buf.len() {
                    self.buf[self.len] = c;
                    self.len += 1;
                }
            }
        }
        fn dec(&mut self, v: i64) {
            if v < 0 {
                self.bytes(b"-");
            }
            let mut n = v.unsigned_abs();
            let mut d = [0u8; 20];
            let mut i = d.len();
            loop {
                i -= 1;
                d[i] = b'0' + (n % 10) as u8;
                n /= 10;
                if n == 0 {
                    break;
                }
            }
            self.bytes(&d[i..]);
        }
        fn hex(&mut self, v: u64) {
            self.bytes(b"0x");
            let mut d = [0u8; 16];
            for (i, x) in d.iter_mut().enumerate() {
                *x = b"0123456789abcdef"[((v >> (60 - 4 * i)) & 0xf) as usize];
            }
            self.bytes(&d);
        }
        fn emit(&self) {
            unsafe { libc::write(2, self.buf.as_ptr().cast(), self.len) };
        }
    }

    /// Copy a small /proc file to stderr (open/read/write/close are async-signal-safe).
    unsafe fn copy_file(path: &[u8], line: Option<&mut Line>) {
        let fd = unsafe { libc::open(path.as_ptr().cast(), libc::O_RDONLY | libc::O_CLOEXEC) };
        if fd < 0 {
            return;
        }
        let mut chunk = [0u8; 2048];
        match line {
            Some(l) => {
                let n = unsafe { libc::read(fd, chunk.as_mut_ptr().cast(), chunk.len()) };
                if n > 0 {
                    let s = &chunk[..n as usize];
                    l.bytes(s.strip_suffix(b"\n").unwrap_or(s));
                }
            }
            None => loop {
                let n = unsafe { libc::read(fd, chunk.as_mut_ptr().cast(), chunk.len()) };
                if n <= 0 {
                    break;
                }
                unsafe { libc::write(2, chunk.as_ptr().cast(), n as usize) };
            },
        }
        unsafe { libc::close(fd) };
    }

    extern "C" fn on_fault(sig: libc::c_int, info: *mut libc::siginfo_t, ctx: *mut libc::c_void) {
        unsafe {
            let code = (*info).si_code;
            let mut l = Line { buf: [0; 512], len: 0 };
            l.bytes(b"\nparalean-p2: fatal signal ");
            l.dec(sig as i64);
            l.bytes(b" code ");
            l.dec(code as i64);
            if code > 0 {
                l.bytes(b" addr ");
                l.hex((*info).si_addr() as u64);
            } else {
                l.bytes(b" sent-by-process");
            }
            #[cfg(target_arch = "x86_64")]
            if !ctx.is_null() {
                let uc = ctx as *const libc::ucontext_t;
                l.bytes(b" ip ");
                l.hex((*uc).uc_mcontext.gregs[libc::REG_RIP as usize] as u64);
                l.bytes(b" sp ");
                l.hex((*uc).uc_mcontext.gregs[libc::REG_RSP as usize] as u64);
            }
            #[cfg(not(target_arch = "x86_64"))]
            let _ = ctx;
            l.bytes(b" pid ");
            l.dec(libc::getpid() as i64);
            l.bytes(b" tid ");
            l.dec(libc::syscall(libc::SYS_gettid) as i64);
            l.bytes(b" thread ");
            copy_file(b"/proc/thread-self/comm\0", Some(&mut l));
            l.bytes(b" stage ");
            l.bytes(match STAGE.load(Ordering::SeqCst) {
                0 => b"run".as_slice(),
                1 => b"runtime-dropped",
                2 => b"fdb-stopping",
                3 => b"fdb-stopped",
                _ => b"?",
            });
            l.bytes(b"\nparalean-p2: /proc/self/maps follows\n");
            l.emit();
            copy_file(b"/proc/self/maps\0", None);
            let i = if sig == libc::SIGSEGV { 0 } else { 1 };
            if code <= 0 {
                // Sent by kill/tgkill: nothing re-executes, so take the default action now.
                let mut dfl: libc::sigaction = std::mem::zeroed();
                dfl.sa_sigaction = libc::SIG_DFL;
                libc::sigaction(sig, &dfl, std::ptr::null_mut());
                libc::raise(sig);
            } else {
                // A hardware fault re-executes under the previous action.
                let prev = std::ptr::addr_of!(PREVIOUS[i]);
                libc::sigaction(sig, (*prev).as_ptr(), std::ptr::null_mut());
            }
        }
    }

    pub fn install() {
        unsafe {
            for (i, &sig) in SIGNALS.iter().enumerate() {
                let mut act: libc::sigaction = std::mem::zeroed();
                act.sa_sigaction = on_fault as *const () as usize;
                act.sa_flags = libc::SA_SIGINFO | libc::SA_ONSTACK;
                libc::sigemptyset(&mut act.sa_mask);
                let prev = std::ptr::addr_of_mut!(PREVIOUS[i]);
                libc::sigaction(sig, &act, (*prev).as_mut_ptr());
            }
        }
    }
}

/// Install the crash reporter if `PARALEAN_SEGV_REPORT=1`.
pub fn install_from_env() {
    if std::env::var("PARALEAN_SEGV_REPORT").as_deref() == Ok("1") {
        #[cfg(target_os = "linux")]
        imp::install();
    }
}
