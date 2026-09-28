# ASM2 verification

Checked at 2026-09-28 10:13:34 UTC, code through `e41e6132` on `task/asm2`.

`PNat.pow_add_pow_ne_pow` now applies
`PNat.pow_add_pow_ne_pow_of_three_inputs`. The adapters in
`FLT/Assembly/ExistingInputs.lean` use `mazur_W`, `lifts`, and
`mem_isCompatible`. The assembly supplies the domain-valued three-adic trace
through the proved sorting and character-purity chain.

The theorem statement is unchanged. The older non-domain three-adic endpoint
is not reachable from this final theorem. Its original declaration is unchanged.

## Checks

- `LEAN_NUM_THREADS=1 lake build FLT FLTTest FermatsLastTheorem`: exit 0,
  9,973 jobs, no warnings. Log: `/tmp/asm2-full-build.log`.
- `FLTTest.AssemblyAxioms` recursively checks both types and bodies, requires
  exactly the three arithmetic leaves below, and rejects the old three-adic
  endpoint. It is imported by the standard test entry point.
- `LEAN_NUM_THREADS=1 lake env lean /tmp/Asm2Audit.lean`: exit 0. It prints
  the recursive audit and runs all 15 default declaration linters, including
  slow checks, on the three adapters and the rewritten final theorem.
- All changed Lean files have lines of at most 100 characters; the diff has
  no whitespace errors or new proof placeholders or foundational declarations.
- `FLT.lean` has all 986 imports, sorted in C-locale order, matching the 986
  Lean files under `FLT/` exactly.

The whole-project declaration-linter attempt was stopped when its Lean process
and Lake together exceeded the 10 GiB budget. The changed-declaration run above
passed; no whole-project declaration-lint result is claimed.

## Recursive audit output

```text
'PNat.pow_add_pow_ne_pow' depends on axioms: [Mazur_statement, propext, sorryAx, Classical.choice, Quot.sound]
AXIOM propext
AXIOM Classical.choice
AXIOM Quot.sound
AXIOM Mazur_statement
DIRECT_ADMISSION GaloisRepresentation.IsHardlyRamified.lifts
AXIOM sorryAx
DIRECT_ADMISSION GaloisRepresentation.IsHardlyRamified.mem_isCompatible
Visited 133413 declarations
-- Found 0 errors in 4 declarations (plus 0 automatically generated ones) in the changed arithmetic declarations with 15 linters
```

All commits are local; nothing was pushed.
