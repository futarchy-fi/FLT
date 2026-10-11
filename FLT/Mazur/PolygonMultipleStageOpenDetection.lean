/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonMultipleVeroneseGeometry
public import FLT.Mazur.PolygonCompleteClosedSpecialization

/-!
# Original closed stages detect open covers at every exact multiple

Proper specialization and the proved original stage comparison show that an
open containing the original zeroth stage contains the whole complete model.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] originalStageToMultipleProj family
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (q : ℕ) [NeZero q] (hq : exactVeroneseStep K n h ∣ q)

/-- Every complete point specializes into the actual original zeroth stage at a common step. -/
theorem exists_multipleStage_specialization (y : Proj (compatibleVeroneseGrade K n h q)) :
    ∃ x : (family K 0 n h).left, y ⤳ originalStageToMultipleProj K n h q hq 0 x := by
  obtain ⟨r, rfl⟩ := hq
  have hr : r ≠ 0 := by
    intro hr
    apply NeZero.ne (exactVeroneseStep K n h * r)
    simp only [hr, Nat.mul_zero]
  let _ : NeZero r := ⟨hr⟩
  let e := multipleVeroneseProjIso K n h (exactVeroneseStep K n h) r (NeZero.pos r)
  obtain ⟨x, hx⟩ := exists_completeClosedFiber_specialization K n h (e.inv y)
  have he := hx.map e.hom.continuous
  have hid : e.hom (e.inv y) = y := by
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
    rfl
  rw [hid] at he
  refine ⟨specialFiberInclusion K 0 n h x, ?_⟩
  have hc := congrArg (fun k ↦ k (specialFiberInclusion K 0 n h x))
    (originalStageToMultipleProj_comparison K n h (exactVeroneseStep K n h) r (dvd_refl _) 0)
  rw [originalStageToMultipleProj_exact] at hc
  exact hc ▸ he

/-- An open containing the original zeroth stage is the entire complete model. -/
theorem multipleStage_open_eq_top (U : (Proj (compatibleVeroneseGrade K n h q)).Opens)
    (hU : originalStageToMultipleProj K n h q hq 0 ⁻¹ᵁ U = ⊤) : U = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨x, hx⟩ := exists_multipleStage_specialization K n h q hq y
  apply hx.mem_open U.isOpen
  exact (congrArg (fun V ↦ x ∈ V) hU).mpr trivial

end FLT.Mazur.PolygonInfinitesimalStages
