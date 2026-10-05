/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodePointCoordinates
public import FLT.Mazur.EllipticComponentQuotient

/-!
# Component labels on actual generic points of a deep split model

The data below are coefficient and uniformizer conditions. They do not assume
any classification or group law for the labels. The label is zero on E₀ and
is the signed common coordinate depth elsewhere. Its zero fiber is exactly E₀;
additivity is a further obligation before this function can descend to E/E₀.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

/-- Explicit coefficient conditions on a split node of exact positive depth n. -/
structure SplitNodeDepth {R : Type*} [CommRing R] [IsLocalRing R]
    (W : WeierstrassCurve R) (π : R) (n : ℕ) : Prop where
  depth_pos : 0 < n
  uniformizer_ne_zero : π ≠ 0
  maximalIdeal_eq : maximalIdeal R = Ideal.span {π}
  a₁_unit : IsUnit W.a₁
  a₂_mem : W.a₂ ∈ maximalIdeal R
  a₃_mem : W.a₃ ∈ maximalIdeal R ^ (n + 1)
  a₄_mem : W.a₄ ∈ maximalIdeal R ^ (n + 1)
  a₆_mem : W.a₆ ∈ maximalIdeal R ^ n
  a₆_not_mem : W.a₆ ∉ maximalIdeal R ^ (n + 1)

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)

/-- The component label function on the actual generic group; additivity is not assumed. -/
noncomputable def nodePointLabel (P : (W.map (algebraMap A K)).toProjective.Point) : ZMod n := by
  classical
  exact if h : SmoothReduction A W P then 0 else
    let v := (exists_nodePointCoordinates A W π D.maximalIdeal_eq n
      D.a₃_mem D.a₄_mem D.a₆_not_mem P h).choose
    nodeBranchLabel n v.depth v.b

/-- Every coordinate witness computes the same label, including smooth integral points. -/
theorem nodePointLabel_eq_of_coordinates {P : (W.map (algebraMap A K)).toProjective.Point}
    (v : NodePointCoordinates A W π P) :
    nodePointLabel D P = nodeBranchLabel n v.depth v.b := by
  classical
  unfold nodePointLabel
  split_ifs with h
  · have hk := (v.smooth_iff
      (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
      (Ideal.pow_le_self (by omega) D.a₃_mem)
      (Ideal.pow_le_self (by omega) D.a₄_mem)
      (Ideal.pow_le_self (Nat.ne_of_gt D.depth_pos) D.a₆_mem)).mp h
    simp [hk]
  · obtain ⟨hk, _, hb⟩ := ((exists_nodePointCoordinates A W π D.maximalIdeal_eq n
      D.a₃_mem D.a₄_mem D.a₆_not_mem P h).choose).unique
      D.uniformizer_ne_zero D.maximalIdeal_eq v
    dsimp only
    rw [hk, hb]

/-- The zero fiber of the label is exactly the actual nonsingular-reduction locus. -/
theorem nodePointLabel_eq_zero_iff (P : (W.map (algebraMap A K)).toProjective.Point) :
    nodePointLabel D P = 0 ↔ SmoothReduction A W P := by
  classical
  by_cases h : SmoothReduction A W P
  · simp [nodePointLabel, h]
  · obtain ⟨v, hv⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
      D.a₃_mem D.a₄_mem D.a₆_not_mem P h
    rw [nodePointLabel_eq_of_coordinates D v, nodeBranchLabel_eq_zero_iff D.depth_pos hv]
    exact (v.smooth_iff
      (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
      (Ideal.pow_le_self (by omega) D.a₃_mem)
      (Ideal.pow_le_self (by omega) D.a₄_mem)
      (Ideal.pow_le_self (Nat.ne_of_gt D.depth_pos) D.a₆_mem)).symm

/-- In particular, the identity has label zero. -/
@[simp] theorem nodePointLabel_zero : nodePointLabel D 0 = 0 :=
  (nodePointLabel_eq_zero_iff D 0).mpr (smoothReduction_zero A W)

/-- The set-theoretic zero fiber is the actual subgroup E₀. -/
theorem nodePointLabel_eq_zero_iff_mem (P : (W.map (algebraMap A K)).toProjective.Point) :
    nodePointLabel D P = 0 ↔ P ∈ ellipticE0 A W :=
  nodePointLabel_eq_zero_iff D P

end FLT.Mazur
