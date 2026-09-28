/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantMuThreeTorsion

/-!
# The section cocycle of the prescribed constant-three extension

Choose an additive section of the actual quotient. The defect is the kernel
coordinate of `σ • s (σ⁻¹ • w) - s w`, not of `σ • s w - s w`.
Its cocycle formula records the contragredient action on the Hom module.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ThreeAdicPlan.FiniteFlatExtension

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

variable {X : FiniteFlatObject ZInvTwo} (E : FiniteFlatExtension constantThree X muThree)

/-- A chosen additive section of the extension's prescribed point quotient. -/
def additiveSection : muThree.points →+ X.points :=
  E.exists_constantThree_muThree_additiveSection.choose

/-- The chosen section is a right inverse of the original quotient map. -/
theorem additiveSection_projection (w : muThree.points) :
    FiniteFlatObject.pointMap E.quotient (E.additiveSection w) = w :=
  E.exists_constantThree_muThree_additiveSection.choose_spec w

/-- The corrected section difference lies in the prescribed kernel. -/
theorem sectionDifference_mem_kernel (σ : Γ) (w : muThree.points) :
    ∃ a : constantThree.points, FiniteFlatObject.pointMap E.inclusion a =
      σ • E.additiveSection (σ⁻¹ • w) - E.additiveSection w := by
  apply (E.pointsExact _).mp
  rw [map_sub, map_smul, E.additiveSection_projection, E.additiveSection_projection,
    smul_inv_smul, sub_self]

/-- The kernel coordinate of the corrected section difference. -/
def sectionDefect (σ : Γ) : muThree.points →+ constantThree.points where
  toFun w := (E.sectionDifference_mem_kernel σ w).choose
  map_zero' := by
    apply E.pointsInjective
    rw [(E.sectionDifference_mem_kernel σ 0).choose_spec]
    simp
  map_add' w v := by
    apply E.pointsInjective
    rw [(FiniteFlatObject.pointMap E.inclusion).map_add,
      (E.sectionDifference_mem_kernel σ (w + v)).choose_spec,
      (E.sectionDifference_mem_kernel σ w).choose_spec,
      (E.sectionDifference_mem_kernel σ v).choose_spec]
    simp only [smul_add, map_add]
    abel

/-- The defect reconstructs the full Galois conjugation of the chosen section. -/
theorem sectionDefect_spec (σ : Γ) (w : muThree.points) :
    FiniteFlatObject.pointMap E.inclusion (E.sectionDefect σ w) =
      σ • E.additiveSection (σ⁻¹ • w) - E.additiveSection w :=
  (E.sectionDifference_mem_kernel σ w).choose_spec

/-- The extension cocycle law, with the inverse action on the argument retained. -/
theorem sectionDefect_mul (σ τ : Γ) (w : muThree.points) :
    E.sectionDefect (σ * τ) w = E.sectionDefect τ (σ⁻¹ • w) + E.sectionDefect σ w := by
  apply E.pointsInjective
  rw [map_add, E.sectionDefect_spec, E.sectionDefect_spec, E.sectionDefect_spec]
  have h := congrArg (fun x : X.points ↦ σ • x) (E.sectionDefect_spec τ (σ⁻¹ • w))
  rw [← map_smul, constantThree_smul, E.sectionDefect_spec] at h
  rw [h]
  simp only [mul_smul, mul_inv_rev, smul_sub]
  abel

/-- The identity automorphism has zero defect. -/
theorem sectionDefect_one : E.sectionDefect 1 = 0 := by
  ext w
  apply E.pointsInjective
  rw [E.sectionDefect_spec]
  simp

/-- Triviality of the section defect is exactly equivariance of that section. -/
theorem sectionDefect_eq_zero_iff :
    (∀ σ : Γ, E.sectionDefect σ = 0) ↔
      ∀ (σ : Γ) (w : muThree.points), E.additiveSection (σ • w) = σ • E.additiveSection w := by
  constructor
  · intro h σ w
    have hd := E.sectionDefect_spec σ (σ • w)
    rw [h σ, AddMonoidHom.zero_apply, map_zero, inv_smul_smul] at hd
    exact (sub_eq_zero.mp hd.symm).symm
  · intro h σ
    ext w
    apply E.pointsInjective
    rw [E.sectionDefect_spec, ← h, smul_inv_smul]
    simp

include E in
/-- An element of the point-action kernel fixes the quotient as well. -/
theorem quotient_fixed_of_pointKernel (σ : Γ) (hσ : σ ∈ X.points.pointActionKernel)
    (w : muThree.points) : σ • w = w := by
  obtain ⟨x, rfl⟩ := E.pointsSurjective w
  rw [← map_smul, (X.points.mem_pointActionKernel σ).mp hσ x]

/-- The cocycle vanishes on the actual middle group's point-action kernel. -/
theorem sectionDefect_eq_zero_of_pointKernel (σ : Γ) (hσ : σ ∈ X.points.pointActionKernel) :
    E.sectionDefect σ = 0 := by
  ext w
  apply E.pointsInjective
  rw [E.sectionDefect_spec, E.quotient_fixed_of_pointKernel σ⁻¹
    (X.points.pointActionKernel.inv_mem hσ),
    (X.points.mem_pointActionKernel σ).mp hσ, sub_self, AddMonoidHom.zero_apply, map_zero]

end ThreeAdicPlan.FiniteFlatExtension
