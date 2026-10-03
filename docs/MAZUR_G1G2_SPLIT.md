# W24: consume polygon geometry in the boundary level problem

Checked at 2026-10-03 11:25 UTC at base `17dcaf85`; main was `f3240f4b`.
The [goal ledger](MAZUR_GOAL_LEDGER.md#w24-gate-audit--polygon-geometry-is-available-arithmetic-is-not)
records the main/branch distinction and every remaining G1/G2/A1–A5 gate.
This replaces the obsolete R1–R3 dispatch: those rotations and the entire
G5/U/H geometry sequence are implemented on the branch.

## Consumer and boundary

The next concrete consumer is the boundary example required by G1-A1 and
G1-A6 of [MAZUR_CONTRACTS](MAZUR_CONTRACTS.md): an actual classified
genus-one polygon family, with a finite flat relative Cartier divisor
whose support meets every irreducible component. Choose one unit on each
normalization component. The all-one choice is the intended support for
the future constant cyclic subgroup of the split n-gon.

This release does **not** call that divisor a subgroup or a level structure.
Rank n, subgroup operations, cyclic divisor equality, moduli pullback and
line-bundle ampleness require further proofs. The field-valued construction
is a boundary test case, not a family over the integral modular base.
Sources: DR II.1.1, II.1.4 and II.1.12 for the polygon/family/action;
the level-structure construction obligations and source ledger in
MAZUR_CONTRACTS G1-A4–A6; Stacks 062Y/0B8U as used by the existing
`SmoothOpenSectionCartier`/`RelativeSums` producers.

## Ordered leaves (caps include all headers/helpers)

All modules are new under `FLT/Mazur/`; no conclusions are supplied as
record fields. These are Lean sketches against named existing APIs; the
release table below will record build-checked final signatures/results.
Common context for polygon leaves:

```lean
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.PolygonPinching
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C)
  (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
```

1. **C1 `PolygonClassifiedFamily`, cap 100, ready.** Import
   `PolygonGeometricGenus` and `ClassifiedGenusOneFamily`.

   ```lean
   theorem classified : FCurve.DRFiberClassification.ClassifiedGeometricFibers C.hom
   theorem family : FCurve.ClassifiedGenusOneFamily C.hom
   theorem baseChange {T : Scheme} (g : T ⟶ Spec (.of K)) :
       FCurve.ClassifiedGenusOneFamily (pullback.snd C.hom g)
   ```

   For every geometric square use `PolygonFieldExtension.exists_cocone_of_isPullback`;
   build its nodal core with `PolygonNodalCore.nodalFiberCore` and its polygon
   witness with that cocone. Properness is `PolygonProper.proper`, flatness
   is over a field, genus is `PolygonGeometricGenus.geometricFibers`.
   This proves the existing contract, not a general classification theorem.

2. **C2 `MultiplicativeGroupDimension`, cap 120, ready.** Import
   `MultiplicativeGroupScheme`, standard-smooth algebra and polynomial equivalence APIs.

   ```lean
   theorem standardSmooth_laurent (R : Type u) [CommRing R] :
       Algebra.IsStandardSmoothOfRelativeDimension 1 R R[T;T⁻¹]
   instance dimension (R : Type u) [CommRing R] :
       SmoothOfRelativeDimension 1 (MultiplicativeGroupScheme.gm R).hom
   ```

   Transfer the one-variable polynomial presentation from `MvPolynomial (Fin 1)`,
   compose with localization away from X (relative dimension zero), then
   use the scheme/ring property bridge. Supplies the precise hypothesis of
   `smoothOpenSectionCartier`; bare smoothness is insufficient.

3. **C3 `PolygonMarkedSections`, cap 180, after C2.** Import C2,
   `PolygonActionTranslation` and `PolygonComponentDistinct`.

   ```lean
   def sectionMap (a : Kˣ) (i : Fin n) : Spec (.of K) ⟶ C.left
   theorem section_base (a : Kˣ) (i : Fin n) : sectionMap K n p a i ≫ C.hom = 𝟙 _
   theorem section_cartier (a : Kˣ) (i : Fin n) :
       FCurve.RelativeEffectiveCartier C.hom (sectionMap K n p a i).ker
   theorem section_disjoint (a b : Kˣ) {i j : Fin n} (hij : i ≠ j) :
       Disjoint (Set.range (sectionMap K n p a i)) (Set.range (sectionMap K n p b j))
   ```

   Construct by `unitPoint` followed by the actual Laurent open of component i;
   prove the section equation by `Over.w`. Apply C2 and the smooth-open
   Cartier theorem, using the open immersion and polygon separatedness.
   Disjointness uses the actual disjoint Laurent charts, including n=1.

4. **C4 `PolygonBoundaryDivisor`, cap 180, after C1/C3.** Import C3 and
   `SectionSumFinite` (C1 provides the family interpretation).

   ```lean
   def ideal (a : Fin n → Kˣ) : C.left.IdealSheafData :=
     ∏ i, (PolygonMarkedSections.sectionMap K n p (a i) i).ker
   theorem cartier (a : Fin n → Kˣ) : FCurve.RelativeEffectiveCartier C.hom (ideal K n p a)
   theorem finite (a : Fin n → Kˣ) : IsFinite ((ideal K n p a).subschemeι ≫ C.hom)
   theorem meetsEveryComponent (a : Fin n → Kˣ) : FCurve.MeetsEveryComponent (ideal K n p a)
   ```

   Reuse Cartier products and proper-family section-sum finiteness. For each
   *actual* irreducible component use `PolygonComponentImages.components_eq`
   and the chosen section point; `mem_support_prod` gives support membership.
   Flatness is part of the Cartier result. No level-structure record is assumed.

## Next gates, not dispatched as small proof leaves

- Identify the all-one divisor subscheme with the constant cyclic group,
  prove finite locally free **rank n**, restrict multiplication/inversion,
  and prove cyclicity and pullback compatibility. Then prove the required
  geometric support/line-bundle ampleness comparison. Split these after
  complete prototypes; a cap for the whole theory would be misleading.
- Assemble the relative generalized-curve category (group/action and
  geometric graph condition), its isomorphisms and pullback. Add finite
  locally free cyclic subgroup data of rank p and the correct moduli presheaf.
- Construct coarse compactification and cusps, then actual Néron reduction
  and cusp specialization; G1 remains open until these producers exist.
- G2 requires Picard/Jacobian, Hecke, completion-kernel quotient, nonzero
  cusp image and arithmetic finiteness. Reuse `GenericFibers` consumers.
- A1 may proceed independently after general-E local APIs are specified;
  A2 depends on G1/G2/A1, A3 on A1/A2, A4 on A3 and Herbrand/class field
  theory, A5 on A4/G2 and geometric isogenies plus the twist-fiber argument.
- Only a clean unconditional `NoLargePrimeTorsion` proof permits the final
  adapter rewire and `PNat.pow_add_pow_ne_pow` axiom check. That existing-file
  edit is outside this release. Older large line/time envelopes are not caps.

## Acceptance

Commit this gate map before implementing the leaves. For each new module run
foreground `LEAN_NUM_THREADS=2 lake build MODULE`, then foreground
`LEAN_NUM_THREADS=2 lake exe runLinter MODULE`, one module at a time.
Audit every originating declaration (including helpers) with `collectAxioms`;
allow only `propext`, `Classical.choice`, `Quot.sound`. No whole-library lint,
no new admission, no existing Lean edits except C-sorted `FLT.lean` imports.
Keep prototypes/logs/handoffs untracked at the root; commit locally and do not push.
