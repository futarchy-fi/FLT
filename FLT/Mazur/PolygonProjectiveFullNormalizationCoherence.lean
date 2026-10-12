/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonProjectiveNormalizedParameter
public import FLT.Mazur.UniversalWeierstrassCyclicFullNaturality

/-!
# Independent normalization recovers the retained original polygon parameter

The full sourcewise construction agrees with the actual normalized polygon
parameter on every original test. The coefficient map and chosen Cartesian
square, infinity label, unit two and coprimality hypotheses are retained.
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

/-- Independent normalization of the original full polygon point is its exact slice parameter. -/
theorem completeProjectiveFullParameter_normalization
    (hn : Nat.Coprime 4 n) (i : Fin n) {T : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) :
    cyclicSchemeNormalizedSlicePoint n
        (completeProjectiveUniversalFullParameter K n h L a ha p q hs h2 hn i f).left =
      completeProjectiveNormalizedFullParameter K n h L a ha p q hs h2 hn i f :=
  cyclicSchemeNormalizedSlicePoint_eq_natural n _

/-- Independent full normalization retains every original test pullback of the polygon family. -/
theorem completeProjectiveFullParameter_normalization_natural
    (hn : Nat.Coprime 4 n) (i : Fin n) {T U : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) (k : U ⟶ T) :
    cyclicSchemeNormalizedSlicePoint n
        (k.left ≫ (completeProjectiveUniversalFullParameter
          K n h L a ha p q hs h2 hn i f).left) =
      completeProjectiveNormalizedFullParameter K n h L a ha p q hs h2 hn i (k ≫ f) := by
  rw [cyclicSchemeNormalizedSlicePoint_natural,
    completeProjectiveFullParameter_normalization]
  exact completeProjectiveNormalizedFullParameter_natural K n h L a ha p q hs h2 hn i f k

end FLT.Mazur.PolygonInfinitesimalStages
