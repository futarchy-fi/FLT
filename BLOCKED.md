# R1d: extension existence remains open

The requested `raynaud_extend_generic_morphism` theorem is **not proved**.
The new `FLT/GroupScheme/RaynaudExtensionExists.lean` proves the graph construction
without adding any extension or rigidity hypothesis.

## Proved

All names below are in `ThreeAdicPlan`.

- `GenericGaloisHom.toBialgHom` constructs the generic Hopf morphism from the
  prescribed equivariant additive map. `toBialgHom_points` verifies its action
  on the original chosen points. Injectivity and surjectivity of the point map
  give surjectivity and injectivity, respectively, of the coordinate map.
- `FF.prod`, `FF.fst`, and `FF.snd` construct the actual tensor-product model
  and its integral projections, with their generic-point comparisons.
- `GenericGaloisHom.closure` constructs the schematic closure of an embedded
  generic subgroup. Its coordinate ring is the quotient by the contracted
  generic kernel; it is finite flat and Hopf, and `closureGenericEquiv`
  identifies its generic fibre with that of the source.
  `genericHom_closureInclusion` verifies the prescribed embedding.
- `GenericGaloisHom.graphClosure`, `graphFst`, and `graphSnd` give the finite
  flat closure of the graph and both integral projections. On the chosen
  points these projections are the identity and the original morphism.
- `graphFst_baseChange_bijective` proves that the first projection is a generic
  isomorphism. `graphFst_injective` proves injectivity on integral coordinate
  rings. `graphClosure_killedByPowerOf` preserves the source's annihilating
  power. `exists_generic_graph_span` packages the resulting span.

These results hold over a Dedekind domain with its fraction field perfect.
The three-adic specialization was also checked by Lean.

## Exact remaining gap

For `X Y : FF ℤ_[3] ℚ_[3]`, `hkX : KilledByPowerOf 3 X`,
`hkY : KilledByPowerOf 3 Y`, and `f : GenericGaloisHom X Y`, one must prove

```lean
Function.Surjective f.graphFst
```

Here `f.graphFst` is the **coordinate ring map**
`X.CoordinateRing →ₐc[ℤ_[3]] f.graphClosure.CoordinateRing`.
Its injectivity and its bijectivity after base change are already proved.
This is the integral rigidity step of Raynaud's theorem, using
`e(ℚ₃/ℚ₃) = 1 < 3 - 1`. A suitable general theorem would assert that a generic
isomorphism between finite flat group schemes killed by powers of three over
`ℤ_[3]` is an integral isomorphism.

With that proof, `BialgEquiv.ofBijective` inverts `f.graphFst`; composing the
inverse with `f.graphSnd` gives the desired integral morphism. The proved
point-comparison and composition lemmas give its generic restriction, and
`raynaud_extend_generic_morphism_unique` supplies uniqueness.

The remaining statement is not encoded as an axiom or assumed in a theorem.
Generic bijectivity and flatness alone do not establish integral surjectivity;
the ramification bound has not been used in the completed construction.
The existing schematic-closure machinery therefore cannot finish the target
without a new proof of the small-ramification theorem. Searching `FLT/` and
mathlib for Raynaud/Oort–Tate found no such rigidity theorem; the order-prime
classification statement in `FLT/MazurChapter/AdmissibleGroupSchemes.lean` is
unproved (`sorry`) and concerns models over `ℤ`, not the needed general
classification over `ℤ_[3]`.

## Verification

Checked at 2026-09-27 22:31 UTC:

- `lake build FLT.GroupScheme.RaynaudExtensionExists`: exit 0, no warnings.
- `lake lint -- --no-build FLT.GroupScheme.RaynaudExtensionExists`: exit 0,
  “Linting passed”.
- `lake env lean /tmp/r1d-axioms.lean`: exit 0. The scratch file imports the
  new module and runs `#print axioms` for all 34 new named declarations
  (including every theorem, definition, and instance). Each uses only
  `propext`, `Classical.choice`, and `Quot.sound`. It also checks the generic
  first-projection isomorphism and annihilating-power preservation specialized
  to `ℤ_[3]` and `ℚ_[3]`.
- `FLT.lean` imports match exactly the 604 `.lean` files under `FLT/`, in
  bytewise (`LC_ALL=C`) order.
- No `sorry`, `axiom`, `admit`, or `native_decide` occurs in the new Lean file.

The build, lint, and axiom output are in `/tmp/r1d-build.log`,
`/tmp/r1d-lint.log`, and `/tmp/r1d-axioms.log` in this workspace environment.
