//! Role-specific key files. A key file holds seeds, and holding a seed is holding that
//! role (`paralean_store::sign::KeyFile`). Each P3 process gets a file with only its own
//! seed and every public key: a validator its validator seed, the controller the
//! authority seed, a worker its workspace seed. Each role refuses a file with any other
//! seed, so a compromised validator or worker cannot expose the authority seed.
//! `paralean-p3 keys export` writes such a file from a full one.

use paralean_store::KeyFile;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    Validator,
    Controller,
    Worker,
}

impl Role {
    pub fn parse(s: &str) -> Result<Role, String> {
        match s {
            "validator" => Ok(Role::Validator),
            "controller" => Ok(Role::Controller),
            "worker" => Ok(Role::Worker),
            other => Err(format!("unknown role {other} (validator, controller, worker)")),
        }
    }
    fn needs_name(self) -> bool {
        self != Role::Controller
    }
}

/// Every seed of `kf` other than `role` (named `name`) needs, as `kind name` strings.
fn foreign_seeds(kf: &KeyFile, role: Role, name: &str) -> Vec<String> {
    let mut out = Vec::new();
    if kf.authority.is_some() && role != Role::Controller {
        out.push("authority".to_string());
    }
    for (kind, entries, own) in [
        ("validator", &kf.validators, role == Role::Validator),
        ("workspace", &kf.workspaces, role == Role::Worker),
        ("job issuer", &kf.job_issuers, false),
    ] {
        for (n, e) in entries {
            if e.seed.is_some() && !(own && n == name) {
                out.push(format!("{kind} {n}"));
            }
        }
    }
    out
}

/// The key file for `role` (and its `name`): every public key, only that role's seed.
pub fn export(kf: &KeyFile, role: Role, name: Option<&str>) -> Result<KeyFile, String> {
    let name = name.unwrap_or("");
    if role.needs_name() && name.is_empty() {
        return Err(format!("--name is required for role {role:?}"));
    }
    let mut out = kf.clone();
    let own = match role {
        Role::Controller => out.authority.is_some(),
        Role::Validator => out.validators.get(name).is_some_and(|e| e.seed.is_some()),
        Role::Worker => out.workspaces.get(name).is_some_and(|e| e.seed.is_some()),
    };
    if !own {
        return Err(format!("the key file holds no seed for {role:?} {name}"));
    }
    if role != Role::Controller {
        out.authority = None;
    }
    for (entries, keep) in [(&mut out.validators, role == Role::Validator), (&mut out.workspaces, role == Role::Worker)] {
        for (n, e) in entries.iter_mut() {
            if !(keep && n == name) {
                e.seed = None;
            }
        }
    }
    for e in out.job_issuers.values_mut() {
        e.seed = None;
    }
    debug_assert!(foreign_seeds(&out, role, name).is_empty());
    Ok(out)
}

/// Refuse to run `role` (named `name`) from a key file holding seeds it does not need.
pub fn check(kf: &KeyFile, role: Role, name: Option<&str>) -> Result<(), String> {
    if cfg!(feature = "mutate-role-keys-unchecked") {
        return Ok(());
    }
    let foreign = foreign_seeds(kf, role, name.unwrap_or(""));
    if foreign.is_empty() {
        return Ok(());
    }
    Err(format!(
        "the key file holds seeds a {role:?} must not have ({}); write a role file with \
         `paralean-p3 keys export <keys> <out> --role {} --name <name>`",
        foreign.join(", "),
        format!("{role:?}").to_lowercase(),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use paralean_store::Signer;

    fn full() -> KeyFile {
        let mut kf = KeyFile::demo(2);
        kf.add_validator("v1", &Signer::derive("keys-test-v1"));
        kf.add_job_issuer("i0", &Signer::derive("keys-test-i0"));
        kf
    }

    #[test]
    fn roles_refuse_key_files_with_other_roles_seeds() {
        let kf = full();
        // The full file: every role refuses it (the controller for the validator,
        // workspace and issuer seeds; the others for the authority seed as well).
        for (role, name) in [(Role::Validator, Some("v0")), (Role::Worker, Some("w0")), (Role::Controller, None)] {
            let e = check(&kf, role, name).unwrap_err();
            assert!(e.contains("validator v1") || e.contains("workspace w1"), "{role:?}: {e}");
            if role != Role::Controller { assert!(e.contains("authority"), "{role:?}: {e}"); }
        }
        // An exported file: only that role's seed, every public key, the same ring.
        let v0 = export(&kf, Role::Validator, Some("v0")).unwrap();
        check(&v0, Role::Validator, Some("v0")).unwrap();
        assert!(v0.authority.is_none() && v0.authority_signer().is_none());
        assert!(v0.validator_signer("v0").is_some() && v0.validator_signer("v1").is_none());
        assert!(v0.workspaces.values().chain(v0.job_issuers.values()).all(|e| e.seed.is_none()));
        assert_eq!(v0.ring().authority, kf.ring().authority);
        assert_eq!(v0.ring().validators, kf.ring().validators);
        assert_eq!(v0.ring().writers, kf.ring().writers);
        // It is still not a key file for another validator or another role.
        assert!(check(&v0, Role::Validator, Some("v1")).is_err());
        assert!(check(&v0, Role::Worker, Some("w0")).is_err());
        let w0 = export(&kf, Role::Worker, Some("w0")).unwrap();
        check(&w0, Role::Worker, Some("w0")).unwrap();
        assert!(w0.authority.is_none() && w0.workspace("w0").is_some() && w0.workspace("w1").is_none());
        let ctl = export(&kf, Role::Controller, None).unwrap();
        check(&ctl, Role::Controller, None).unwrap();
        assert!(ctl.authority_signer().is_some() && ctl.validators.values().all(|e| e.seed.is_none()));
        // A seed the source file does not hold cannot be exported.
        assert!(export(&v0, Role::Controller, None).is_err());
        assert!(export(&kf, Role::Validator, Some("v9")).is_err());
    }
}
