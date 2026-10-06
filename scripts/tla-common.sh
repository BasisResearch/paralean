# Shared by check-tla.sh, check-tla-negative.sh and archive-verification.sh.
# Sourced from the repository root.

# Positive TLC scenarios. "Name:Module" checks verification/tla/Name.cfg
# against Module.tla; a bare name uses the same name for both.
TLA_SCENARIOS=(Chain Collision Revision Revert Rejected Quorums Integrated
  CheckpointReuse ExportRejected Receipts Targets TargetsLagging:Targets
  TargetsLive:Targets Fencing FencingLive:Fencing Certificates
  CertificatesLagging:Certificates CertificatesLive:Certificates Workspace
  WorkspacePending:Workspace)

# Larger-scope instances of the same models. Too slow for the default suite;
# run with `check-tla.sh --wide`. Logs go to .runs/tla/wide/.
TLA_WIDE_SCENARIOS=(ReceiptsWide:Receipts TargetsWide FencingWide:Fencing
  WorkspaceWide:Workspace)

scenario_name() { printf '%s\n' "${1%%:*}"; }
scenario_module() { if [[ $1 == *:* ]]; then printf '%s\n' "${1#*:}"; else printf '%s\n' "$1"; fi; }

sha256_files() {
  if command -v sha256sum > /dev/null 2>&1; then sha256sum "$@"; else shasum -a 256 "$@"; fi
}

# Copy the TLA sources into a run directory and record their hashes. These are
# the pristine sources a run was derived from (before any mutation).
stage_sources() {
  local dir="$1"
  rm -rf "$dir"
  mkdir -p "$dir"
  cp verification/tla/*.tla verification/tla/*.cfg "$dir/"
  (cd "$dir" && sha256_files *.tla *.cfg > pristine.sha256)
}

# Append to the TLC log the hashes of the pristine sources and of the exact
# files TLC parsed from the run directory plus the configuration it used.
record_provenance() {
  local dir="$1" module="$2" cfg="$3" log="$4" expect="$5"
  local parsed
  parsed="$(sed -n "s#^Parsing file $dir/\\(.*\\.tla\\)\$#\\1#p" "$log" | LC_ALL=C sort -u)"
  if ! grep -qx "$module.tla" <<< "$parsed"; then
    echo "TLC did not parse $dir/$module.tla" >&2
    return 1
  fi
  {
    echo "==== Paralean TLC provenance ===="
    echo "module $module"
    echo "config $cfg.cfg"
    echo "expect $expect"
    # A mutated run also lists the pristine sources it was derived from.
    [[ $expect == pass ]] || sed 's/^/source /' "$dir/pristine.sha256"
    # shellcheck disable=SC2086
    (cd "$dir" && sha256_files $parsed "$cfg.cfg") | sed 's/^/checked /'
    echo "==== end provenance ===="
  } >> "$log"
}
