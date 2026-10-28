#!/usr/bin/env python3
"""Compile the actual Rust authority guard and kill an unconditional-signer mutant.

The live LSP gate separately exercises this command against worker-only keys and
the real store. This fast harness isolates its source guard without rebuilding
the running bridge or touching the store.
"""

from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[3]
SOURCE = (ROOT / "impl/p5/store-bridge/src/targets.rs").read_text()
GUARD = '    let signer = keys.authority_signer().ok_or("authority seed required for revocation")?;'
assert SOURCE.count(GUARD) == 1, "revocation authority guard changed"


def run_guard(line: str, directory: Path) -> subprocess.CompletedProcess:
    source = directory / "guard.rs"
    source.write_text("""
struct Keys { authority_seed: bool }
impl Keys {
    fn authority_signer(&self) -> Option<()> {
        self.authority_seed.then_some(())
    }
}
fn revoke_validator(keys: Keys) -> Result<(), &'static str> {
GUARD_LINE
    let _ = signer;
    Ok(())
}
#[test]
fn worker_seed_cannot_authorize_revocation() {
    assert_eq!(revoke_validator(Keys { authority_seed: false }),
               Err("authority seed required for revocation"));
    assert_eq!(revoke_validator(Keys { authority_seed: true }), Ok(()));
}
""".replace("GUARD_LINE", line))
    binary = directory / "guard-test"
    subprocess.run(["rustc", "--edition=2021", "--test", str(source), "-o", str(binary)],
                   check=True, capture_output=True, text=True)
    return subprocess.run([str(binary)], capture_output=True, text=True)


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="paralean-revoke-mutant-") as raw:
        directory = Path(raw)
        baseline = run_guard(GUARD, directory)
        if baseline.returncode:
            raise AssertionError("source guard baseline failed:\n" + baseline.stdout + baseline.stderr)
        mutant = run_guard(GUARD.replace("keys.authority_signer()", "Some(())"), directory)
        if mutant.returncode == 0 or "worker_seed_cannot_authorize_revocation" not in mutant.stdout:
            raise AssertionError("unconditional-signer source mutant survived")
        print("KILLED Rust revocation authority guard mutant")


if __name__ == "__main__":
    main()
