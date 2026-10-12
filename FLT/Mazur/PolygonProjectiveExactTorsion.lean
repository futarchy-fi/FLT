/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonProjectiveCyclicPoints

/-!
# Exact torsion from the original cyclic marked orbit

The actual labels embed as a cyclic subgroup of the constructed elliptic
field-point group. The next label has order exactly the original polygon size.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))

local notation "P" => completeCartesianProjectiveMarkedPoint K n h L a ha p q hs

/-- The original cyclic labels embed as an actual homomorphism of elliptic point groups. -/
def completeProjectiveCyclicPointHom (i : Fin n) :
    Multiplicative (ZMod n) →* integralGroupFieldPoints (K := L)
      (completeCartesianPointWeierstrass K n h L (Spec.map (CommRingCat.ofHom a)) p q hs i)
      (by
        let _ := completeCartesianPointWeierstrass_isElliptic K n h L a ha p q hs i
        exact WeierstrassCurve.isUnit_Δ _) where
  toFun b := P i (rotateIndex b.toAdd i)
  map_one' := by
    change P i (rotateIndex 0 i) = 1
    rw [rotateIndex_zero, completeCartesianProjectiveMarkedPoint_self]
  map_mul' b c := completeProjectiveMarkedPoint_add K n h L a ha p q hs i b.toAdd c.toAdd

/-- No two original cyclic residues yield the same constructed elliptic point. -/
theorem completeProjectiveCyclicPointHom_injective (i : Fin n) :
    Function.Injective (completeProjectiveCyclicPointHom K n h L a ha p q hs i) := by
  intro b c he
  have hi := completeCartesianProjectiveMarkedPoint_injective K n h L a ha p q hs i he
  have hz := congrArg (ZMod.finEquiv n) hi
  change (ZMod.finEquiv n) ((ZMod.finEquiv n).symm ((ZMod.finEquiv n) i + b.toAdd)) =
    (ZMod.finEquiv n) ((ZMod.finEquiv n).symm ((ZMod.finEquiv n) i + c.toAdd)) at hz
  rw [(ZMod.finEquiv n).apply_symm_apply, (ZMod.finEquiv n).apply_symm_apply] at hz
  have hc : b.toAdd = c.toAdd := add_left_cancel hz
  exact Multiplicative.toAdd.injective hc

/-- The original marking one step after infinity has exactly the original cyclic order. -/
theorem completeProjectiveMarkedPoint_orderOf (i : Fin n) :
    orderOf (P i (rotateIndex (1 : ZMod n) i)) = n := by
  have he := orderOf_injective (completeProjectiveCyclicPointHom K n h L a ha p q hs i)
    (completeProjectiveCyclicPointHom_injective K n h L a ha p q hs i)
    (Multiplicative.ofAdd (1 : ZMod n))
  exact he.trans (ZMod.addOrderOf_one n)

end FLT.Mazur.PolygonInfinitesimalStages
