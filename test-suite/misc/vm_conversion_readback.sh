#!/usr/bin/env bash
set -eu
export PATH="$BIN:$PATH"

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cd "$d"

cat > Readback.v <<'EOF'
Definition hidden_nat (b : bool) := if b then nat else bool.

Profile "direct" Definition direct : nat := (O <: hidden_nat true).
Set VM Conversion Readback.

Goal hidden_nat true.
Proof.
  vm_cast_no_check O.
Profile "readback" Qed.
EOF

rocq c -q -output-directory "$d" Readback.v
# This event surrounds normal conversion on verified residuals in the kernel.
event='"vm_conv_readback_residuals"'
if grep -q "$event" direct.json; then
  echo 'Readback ran with the option unset.' >&2
  exit 1
fi
grep -q "$event" readback.json

# With the VM disabled the same casts should fall back to normal conversion.
rocq c -q -output-directory "$d" -bytecode-compiler no Readback.v
if grep -q "$event" readback.json; then
  echo 'Readback ran with the VM disabled.' >&2
  exit 1
fi
