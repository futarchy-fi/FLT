/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonProjectiveNormalizedParameter
public import FLT.Mazur.UniversalWeierstrassCyclicNaturalFixedPoint

/-!
# Independent normalization fixes the retained polygon full-slice parameter

The actual normalized polygon parameter is fixed by sourcewise full
normalization. This retains the original coefficient map, cartesian square,
infinity label, auxiliary marking, and every cyclic label on all tests.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart UniversalWeierstrass AuxiliaryLevel PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
local notation "W" => completeCartesianPointWeierstrass K n h L
  (Spec.map (CommRingCat.ofHom a)) p q hs

variable (h2 : (2 : L) ≠ 0)
local notation "hΔ" => completeProjectiveEquation_discriminant K n h L a ha p q hs
local notation "base" => originalCoefficientBase
local notation "unitTwo" => Iff.mpr isUnit_iff_ne_zero h2

/-- The actual normalized polygon full point is fixed by independent normalization. -/
theorem completeProjectiveNormalizedFullParameter_fixed
    (hn : Nat.Coprime 4 n) (i : Fin n) {T : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) :
    cyclicSchemeNormalizedPoint n
        (completeProjectiveNormalizedFullParameter K n h L a ha p q hs h2 hn i f ≫
          cyclicNormalizedSliceInclusion n) =
      completeProjectiveNormalizedFullParameter K n h L a ha p q hs h2 hn i f ≫
        cyclicNormalizedSliceInclusion n :=
  cyclicSchemeNormalizedPoint_restrict n _

/-- Independent normalization recovers the exact original full polygon slice parameter. -/
theorem completeProjectiveNormalizedFullParameter_slice_fixed
    (hn : Nat.Coprime 4 n) (i : Fin n) {T : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) :
    cyclicSchemeNormalizedSlicePoint n
        (completeProjectiveNormalizedFullParameter K n h L a ha p q hs h2 hn i f ≫
          cyclicNormalizedSliceInclusion n) =
      completeProjectiveNormalizedFullParameter K n h L a ha p q hs h2 hn i f :=
  cyclicSchemeNormalizedSlicePoint_restrict n _

/-- The independently normalized polygon slice point commutes with original test maps. -/
theorem completeProjectiveNormalizedFullParameter_fixed_natural
    (hn : Nat.Coprime 4 n) (i : Fin n) {T U : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) (k : U ⟶ T) :
    cyclicSchemeNormalizedSlicePoint n
        (k.left ≫ completeProjectiveNormalizedFullParameter K n h L a ha p q hs h2 hn i f ≫
          cyclicNormalizedSliceInclusion n) =
      completeProjectiveNormalizedFullParameter K n h L a ha p q hs h2 hn i (k ≫ f) := by
  rw [← Category.assoc, cyclicSchemeNormalizedSlicePoint_restrict]
  exact completeProjectiveNormalizedFullParameter_natural K n h L a ha p q hs h2 hn i f k

end FLT.Mazur.PolygonInfinitesimalStages
