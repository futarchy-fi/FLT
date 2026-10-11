/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleConicFactor
public import FLT.Mazur.WeierstrassSuccessiveXMiddleNodeBranches

/-!
# The intersection of the full middle nodes lies on their conic branches

The two original tangent denominators force the horizontal coordinate to vanish
on every common test algebra. The divided constant is unrestricted.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] (W : WeierstrassCurve K) (c : K)
  (h2 : W.a₂ = 0) (ha : IsUnit W.a₁)
local notation "A" => Coordinate W 0 0 0 0 c
local notation "N" => MiddleNodeOpen c
local notation "B" => middleFirstToNodeBase W c h2

include ha in
/-- Agreement on the original fiber makes both recentered slopes invertible. -/
theorem middleNode_intersection_slopes_isUnit {S : Type*} [CommRing S]
    (f g : N →+* S)
    (h : f.comp (B).toRingHom =
      g.comp ((B).comp (middleTangentSwitch W c h2)).toRingHom) :
    IsUnit (f (middleNodeV W.a₁ c)) ∧ IsUnit (g (middleNodeV W.a₁ c)) := by
  have hv := DFunLike.congr_fun h (coord W 0 0 0 0 c 1)
  change f (B (coord W 0 0 0 0 c 1)) =
    g (B (middleTangentSwitch W c h2 (coord W 0 0 0 0 c 1))) at hv
  simp only [middleTangentSwitch_coord, Matrix.cons_val_one, Matrix.cons_val_zero,
    map_sub, map_neg, AlgHom.commutes, middleFirstToNodeBase_coord] at hv
  change f (middleNodeV W.a₁ c) =
    -g (middleNodeV W.a₁ c) - g (algebraMap K N W.a₁) at hv
  have hc := DFunLike.congr_fun h (algebraMap K A W.a₁)
  change f (B (algebraMap K A W.a₁)) =
    g (B (middleTangentSwitch W c h2 (algebraMap K A W.a₁))) at hc
  simp only [AlgHom.commutes] at hc
  constructor
  · rw [hv]
    simpa only [map_add, neg_add, sub_eq_add_neg] using
      ((middleNode_v_add_isUnit W.a₁ c ha).map g).neg
  · have he : g (middleNodeV W.a₁ c) =
        -(f (middleNodeV W.a₁ c) + f (algebraMap K N W.a₁)) := by
      rw [hv, hc]
      ring
    rw [he]
    simpa only [map_add] using ((middleNode_v_add_isUnit W.a₁ c ha).map f).neg

include ha in
/-- Both horizontal functions vanish on every common test algebra of the original nodes. -/
theorem middleNode_intersection_horizontal_zero {S : Type*} [CommRing S]
    (f g : N →+* S)
    (h : f.comp (B).toRingHom =
      g.comp ((B).comp (middleTangentSwitch W c h2)).toRingHom) :
    f (middleNodeU c) = 0 ∧ g (middleNodeU c) = 0 := by
  obtain ⟨hf, hg⟩ := middleNode_intersection_slopes_isUnit W c h2 ha f g h
  exact ⟨middleNode_horizontal_eq_zero_of_slope_isUnit c f W.a₁ hf,
    middleNode_horizontal_eq_zero_of_slope_isUnit c g W.a₁ hg⟩

end FLT.Mazur.WeierstrassSuccessiveX
