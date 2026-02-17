#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

if ! command -v docker >/dev/null 2>&1; then
  echo "docker is required but not found" >&2
  exit 1
fi

if ! docker info >/dev/null 2>&1; then
  echo "docker is installed but not usable from this environment" >&2
  echo "check Docker Desktop WSL integration (or run on a host with working docker daemon)" >&2
  exit 1
fi

CONTAINER_NAME="${PG_TEST_CONTAINER:-dbapp-pg-test-$$}"
PG_IMAGE="${PG_TEST_IMAGE:-postgres:16}"
PG_PORT="${PG_TEST_PORT:-55432}"
PG_USER="${PG_TEST_USER:-postgres}"
PG_PASSWORD="${PG_TEST_PASSWORD:-postgres}"
PG_DB="${PG_TEST_DB:-postgres}"
KEEP_CONTAINER="${PG_TEST_KEEP_CONTAINER:-0}"
READY_TIMEOUT="${PG_TEST_READY_TIMEOUT:-180}"
READY_INTERVAL="${PG_TEST_READY_INTERVAL:-1}"
SCRIPT_OK=0

CONNINFO="postgresql://${PG_USER}:${PG_PASSWORD}@127.0.0.1:${PG_PORT}/${PG_DB}"
READY_STABLE_HITS="${PG_TEST_READY_STABLE_HITS:-3}"

cleanup() {
  if [[ "$KEEP_CONTAINER" == "1" || "$SCRIPT_OK" != "1" ]]; then
    echo "keeping container: ${CONTAINER_NAME}"
    return
  fi
  docker rm -f "$CONTAINER_NAME" >/dev/null 2>&1 || true
}
trap cleanup EXIT

if docker ps -a --format '{{.Names}}' | grep -Fxq "$CONTAINER_NAME"; then
  echo "container already exists: $CONTAINER_NAME" >&2
  echo "set PG_TEST_CONTAINER to another name" >&2
  exit 1
fi

echo "starting postgres container: ${CONTAINER_NAME} (${PG_IMAGE})"
docker run --name "$CONTAINER_NAME" \
  -e POSTGRES_USER="$PG_USER" \
  -e POSTGRES_PASSWORD="$PG_PASSWORD" \
  -e POSTGRES_DB="$PG_DB" \
  -p "${PG_PORT}:5432" \
  -d "$PG_IMAGE" >/dev/null

echo "waiting for postgres readiness..."
elapsed=0
stable_hits=0
while [[ "$elapsed" -lt "$READY_TIMEOUT" ]]; do
  if docker exec "$CONTAINER_NAME" pg_isready -h 127.0.0.1 -p 5432 -U "$PG_USER" -d "$PG_DB" >/dev/null 2>&1; then
    stable_hits=$((stable_hits + 1))
    if [[ "$stable_hits" -ge "$READY_STABLE_HITS" ]]; then
      break
    fi
  else
    stable_hits=0
  fi
  sleep "$READY_INTERVAL"
  elapsed=$((elapsed + READY_INTERVAL))
done

if [[ "$stable_hits" -lt "$READY_STABLE_HITS" ]]; then
  echo "postgres did not become ready in time (${READY_TIMEOUT}s, stable_hits=${stable_hits}/${READY_STABLE_HITS})" >&2
  docker logs "$CONTAINER_NAME" | tail -n 120 >&2 || true
  exit 1
fi

echo "running Lean pg smoke test (SELECT 1)"
lake exe db-app-verification --pg-test "$CONNINFO"

echo "pg binding smoke test passed"
SCRIPT_OK=1
