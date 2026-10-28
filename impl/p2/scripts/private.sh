# Helpers for files that carry deployment secrets. Source it; do not execute it.
#
# garage.toml holds Garage's RPC secret, admin and metrics tokens, credentials.sh the S3 key, and
# fdb.cluster FoundationDB's connection string (FDB has no other client authentication;
# its trace logs repeat the string). They are written under umask 077, but a file or
# directory created by an older script keeps its old mode, so every start re-applies it.

# make_private DIR... : owner-only directories, and owner-only files directly inside them.
make_private() {
  local d f
  for d in "$@"; do
    [ -d "$d" ] || continue
    chmod 700 "$d"
    for f in "$d"/*; do [ -f "$f" ] && chmod 600 "$f"; done
  done
  return 0
}

# ensure_metrics_token CREDENTIALS : load a credentials.sh, first adding the bearer token
# Garage's admin /metrics endpoint requires (W2-40) when the file predates it. Without
# `metrics_token` in garage.toml, /metrics answers every local client.
ensure_metrics_token() {
  if ! grep -q '^export PARALEAN_GARAGE_METRICS_TOKEN=' "$1"; then
    ( umask 077
      printf 'export PARALEAN_GARAGE_METRICS_TOKEN=%s\n' "$(head -c 32 /dev/urandom | od -An -tx1 | tr -d ' \n')" >> "$1" )
  fi
  . "$1"
}

# import_app_key ADMIN_PORT : register $PARALEAN_S3_ACCESS_KEY/$PARALEAN_S3_SECRET_KEY with
# Garage through its admin API. `garage key import ID SECRET` would put the secret on a
# command line, which every local user can read in /proc; curl reads the bearer token and
# the request body from owner-only files instead.
import_app_key() {
  local port="$1" tmp code
  tmp="$(umask 077; mktemp -d)"
  ( umask 077
    printf 'Authorization: Bearer %s\n' "$PARALEAN_GARAGE_ADMIN_TOKEN" > "$tmp/header"
    printf '{"accessKeyId":"%s","secretAccessKey":"%s","name":"paralean-app"}' \
      "$PARALEAN_S3_ACCESS_KEY" "$PARALEAN_S3_SECRET_KEY" > "$tmp/body" )
  code="$(curl -s -o "$tmp/response" -w '%{http_code}' -H "@$tmp/header" --data-binary "@$tmp/body" \
    "http://127.0.0.1:$port/v2/ImportKey" || true)"
  rm -rf "$tmp"
  [ "$code" = 200 ] || { echo "Garage key import failed (HTTP $code)" >&2; return 1; }
}
