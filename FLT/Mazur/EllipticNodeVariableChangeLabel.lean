/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeSmallChangeLabel
public import FLT.Mazur.EllipticNodeChangeDepth
public import FLT.Mazur.EllipticNodeTangentSwap

/-!
# Labels under arbitrary integral changes of split depth models

Every change between split models at the same exact depth acts on point
and component labels by a sign. The shear residue determines that sign:
zero preserves the tangents and the other residue exchanges them.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] [DecidableEq K] {A : ValuationSubring K}
  {W : WeierstrassCurve A} [(W.map (algebraMap A K)).IsElliptic]
  {π π' : A} {n : ℕ} (D : SplitNodeDepth W π n) (C : VariableChange A)
  (D' : SplitNodeDepth (C • W) π' n)

/-- A shear exchanging the residual tangents negates actual point labels. -/
theorem nodePointLabel_exchangingChange (hs : C.s + W.a₁ ∈ maximalIdeal A)
    (P : ((C • W).map (algebraMap A K)).toProjective.Point) :
    nodePointLabel D (integralProjectiveVariableChange A W C P) = -nodePointLabel D' P := by
  let D₀ : SplitNodeDepth W π' n :=
    { D with
      uniformizer_ne_zero := D'.uniformizer_ne_zero
      maximalIdeal_eq := D'.maximalIdeal_eq }
  rw [← nodePointLabel_uniformizer_independent D D₀]
  by_cases hp : SmoothReduction A (C • W) P
  · rw [(nodePointLabel_eq_zero_iff D' P).mpr hp,
      (nodePointLabel_eq_zero_iff D₀ _).mpr
        ((integralProjectiveVariableChange_smooth A W C P).mpr hp), neg_zero]
  · obtain ⟨hr, ht⟩ := splitNodeDepth_change_translation_deep D C D'
    obtain ⟨v, hv⟩ := exists_nodePointCoordinates A (C • W) π' D'.maximalIdeal_eq n
      D'.a₃_mem D'.a₄_mem D'.a₆_not_mem P hp
    obtain ⟨ρ, hρ, hr'⟩ := exists_node_deep_factor D'.maximalIdeal_eq v.depth
      (Ideal.pow_le_pow_right (by omega) hr)
    obtain ⟨τ, hτ, ht'⟩ := exists_node_deep_factor D'.maximalIdeal_eq v.depth
      (Ideal.pow_le_pow_right (by omega) ht)
    obtain ⟨w, hk, _, hb⟩ := exists_nodePointCoordinates_integralChange C v hρ hτ hr' ht'
    have hid : (C.u : A) * (C • W).a₁ = W.a₁ + 2 * C.s := by
      rw [variableChange_a₁, ← mul_assoc, Units.mul_inv, one_mul]
    have hdiff : w.b - (C.u : A) ^ 3 * (v.b + (C • W).a₁ * v.a) =
        -(C.u : A) ^ 2 * (C.s + W.a₁) * v.a + τ := by
      rw [hb]
      linear_combination -(C.u : A) ^ 2 * v.a * hid
    have hm0 : w.b - (C.u : A) ^ 3 * (v.b + (C • W).a₁ * v.a) ∈ maximalIdeal A := by
      rw [hdiff]
      exact (maximalIdeal A).add_mem
        ((maximalIdeal A).mul_mem_right _ ((maximalIdeal A).mul_mem_left _ hs)) hτ
    have he := (residue_eq_zero_iff _).mpr hm0
    rw [map_sub, sub_eq_zero] at he
    have hu : residue A (C.u : A) ≠ 0 := (residue_ne_zero_iff_isUnit _).mpr C.u.isUnit
    have hm : w.b ∈ maximalIdeal A ↔ v.b + (C • W).a₁ * v.a ∈ maximalIdeal A := by
      rw [← residue_eq_zero_iff, ← residue_eq_zero_iff, he, map_mul, map_pow, mul_eq_zero]
      simp [pow_ne_zero 3 hu]
    have hl : nodeBranchLabel n w.depth w.b =
        nodeBranchLabel n v.depth (v.b + (C • W).a₁ * v.a) := by
      unfold nodeBranchLabel
      rw [hk]
      congr 1
      exact propext (or_congr Iff.rfl hm)
    rw [nodePointLabel_eq_of_coordinates D₀ w, nodePointLabel_eq_of_coordinates D' v, hl]
    exact nodeTangentSwap_branchLabel (C • W) D' hv v.a v.b v.primitive v.equation

open Classical in
/-- Every integral change between split depth models acts by its residual tangent sign. -/
theorem nodePointLabel_variableChange
    (P : ((C • W).map (algebraMap A K)).toProjective.Point) :
    nodePointLabel D (integralProjectiveVariableChange A W C P) =
      if C.s ∈ maximalIdeal A then nodePointLabel D' P else -nodePointLabel D' P := by
  classical
  by_cases hs : C.s ∈ maximalIdeal A
  · rw [ite_eq_left hs]
    obtain ⟨hr, ht⟩ := splitNodeDepth_change_translation_deep D C D'
    exact nodePointLabel_smallChange D C D' hs hr ht P
  · rw [ite_eq_right hs]
    exact nodePointLabel_exchangingChange D C D'
      ((splitNodeDepth_change_shear_cases D C D').resolve_left hs) P

open Classical in
/-- The actual component equivalence has the same residual tangent sign on labels. -/
theorem nodeComponentLabel_variableChange (c : EllipticComponentQuotient A (C • W)) :
    nodeComponentLabel D (integralComponentVariableChange A W C c) =
      if C.s ∈ maximalIdeal A then nodeComponentLabel D' c else -nodeComponentLabel D' c := by
  classical
  obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A (C • W) c
  rw [integralComponentVariableChange_mk, nodeComponentLabel_mk, nodeComponentLabel_mk]
  exact nodePointLabel_variableChange D C D' P

end FLT.Mazur
