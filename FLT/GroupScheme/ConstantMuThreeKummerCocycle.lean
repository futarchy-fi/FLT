/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantMuThreeSectionCocycle
public import FLT.GroupScheme.CubicKummerCocycle
public import FLT.GroupScheme.MuThreeCubicCoordinates

/-!
# A Kummer parameter for the actual constant-three extension

The corrected section cocycle is evaluated in cube roots of unity and factored
through the finite Galois point field of the original middle group. Hilbert 90
then supplies a nonzero rational parameter and its equivariant cube root in
that same field.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ThreeAdicPlan.FiniteFlatExtension

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

variable {X : FiniteFlatObject ZInvTwo} (E : FiniteFlatExtension constantThree X muThree)

/-- The section defect in cube-root point coordinates. -/
def cubicPointCocycle (σ : Γ) : muThree.points :=
  muThreeCoordinates (E.sectionDefect σ (muThreeCoordinates 1))

/-- The corrected section defect transforms as a cube-root-valued cocycle. -/
theorem cubicPointCocycle_mul (σ τ : Γ) :
    E.cubicPointCocycle (σ * τ) = σ • E.cubicPointCocycle τ + E.cubicPointCocycle σ := by
  unfold cubicPointCocycle
  rw [E.sectionDefect_mul, map_add]
  exact congrArg (· + muThreeCoordinates (E.sectionDefect σ (muThreeCoordinates 1)))
    (muThreeCoordinates_contragredient σ (E.sectionDefect τ))

/-- The cube-root cocycle vanishes on the original middle group's action kernel. -/
theorem cubicPointCocycle_eq_zero_of_pointKernel (σ : Γ)
    (hσ : σ ∈ X.points.pointActionKernel) : E.cubicPointCocycle σ = 0 := by
  simp [cubicPointCocycle, E.sectionDefect_eq_zero_of_pointKernel σ hσ]

/-- The section cocycle depends only on the restriction to the actual point field. -/
theorem cubicPointCocycle_eq_of_restrict_eq (σ τ : Γ)
    (h : AlgEquiv.restrictNormalHom X.points.pointField σ =
      AlgEquiv.restrictNormalHom X.points.pointField τ) :
    E.cubicPointCocycle σ = E.cubicPointCocycle τ := by
  have hk : τ⁻¹ * σ ∈ X.points.pointActionKernel := by
    rw [← X.points.pointField_fixingSubgroup, ← X.points.pointField.restrictNormalHom_ker,
      MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hc := E.cubicPointCocycle_mul τ (τ⁻¹ * σ)
  simpa only [mul_inv_cancel_left, E.cubicPointCocycle_eq_zero_of_pointKernel _ hk,
    smul_zero, zero_add] using hc

include E in
/-- Every cube-root coordinate belongs to the actual middle group's point field. -/
theorem muThreeValue_mem_pointField (w : muThree.points) :
    muThreeValue w ∈ X.points.pointField := by
  rw [FiniteContinuousGaloisModule.pointField, IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have h := congrArg Units.val (muThreeUnit_smul σ w)
  change muThreeValue (σ • w) = σ (muThreeValue w) at h
  rw [← h, E.quotient_fixed_of_pointKernel σ hσ]

/-- Evaluation of the cube-root group in the units of the actual point field. -/
def pointFieldMuThreeUnit : Multiplicative muThree.points →* X.points.pointFieldˣ where
  toFun w := Units.mk0 ⟨muThreeValue w.toAdd, E.muThreeValue_mem_pointField w.toAdd⟩ (by
    intro h
    exact muThreeValue_ne_zero w.toAdd (congrArg Subtype.val h))
  map_one' := by
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val muThreeUnit.map_one
  map_mul' w v := by
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val (muThreeUnit.map_mul w v)

/-- The point-field evaluation has cube one. -/
theorem pointFieldMuThreeUnit_cube (w : muThree.points) :
    E.pointFieldMuThreeUnit (Multiplicative.ofAdd w) ^ 3 = 1 := by
  apply Units.ext
  apply Subtype.ext
  exact muThreeValue_cube w

set_option synthInstance.maxHeartbeats 100000 in
-- The nested point-field unit action needs a larger instance-search budget.
/-- Evaluation in the point field is equivariant for restriction of Galois automorphisms. -/
theorem pointFieldMuThreeUnit_smul (σ : Γ) (w : muThree.points) :
    E.pointFieldMuThreeUnit (Multiplicative.ofAdd (σ • w)) =
      AlgEquiv.restrictNormalHom X.points.pointField σ •
        E.pointFieldMuThreeUnit (Multiplicative.ofAdd w) := by
  apply Units.ext
  apply Subtype.ext
  change muThreeValue (σ • w) =
    ((AlgEquiv.restrictNormalHom X.points.pointField σ)
      (⟨muThreeValue w, E.muThreeValue_mem_pointField w⟩ : X.points.pointField) :
        AlgebraicClosure ℚ)
  rw [AlgEquiv.restrictNormalHom_apply]
  exact congrArg Units.val (muThreeUnit_smul σ w)

/-- A chosen lift of each finite point-field Galois automorphism. -/
def pointFieldGaloisLift (g : Gal(X.points.pointField/ℚ)) : Γ :=
  (AlgEquiv.restrictNormalHom_surjective (K₁ := X.points.pointField) (AlgebraicClosure ℚ) g).choose

/-- The chosen lift restricts to the given finite automorphism. -/
theorem pointFieldGaloisLift_restrict (g : Gal(X.points.pointField/ℚ)) :
    AlgEquiv.restrictNormalHom X.points.pointField (pointFieldGaloisLift (X := X) g) = g :=
  (AlgEquiv.restrictNormalHom_surjective
    (K₁ := X.points.pointField) (AlgebraicClosure ℚ) g).choose_spec

/-- The actual extension cocycle on its finite Galois point field. -/
def finiteCubicCocycle (g : Gal(X.points.pointField/ℚ)) : X.points.pointFieldˣ :=
  E.pointFieldMuThreeUnit
    (Multiplicative.ofAdd (E.cubicPointCocycle (pointFieldGaloisLift (X := X) g)))

/-- Pulling back the finite cocycle recovers the original extension's section defect. -/
theorem finiteCubicCocycle_restrict (σ : Γ) :
    E.finiteCubicCocycle (AlgEquiv.restrictNormalHom X.points.pointField σ) =
      E.pointFieldMuThreeUnit (Multiplicative.ofAdd (E.cubicPointCocycle σ)) := by
  unfold finiteCubicCocycle
  rw [E.cubicPointCocycle_eq_of_restrict_eq _ σ (pointFieldGaloisLift_restrict _)]

/-- The finite cocycle satisfies the multiplicative cocycle identity. -/
theorem finiteCubicCocycle_isMulCocycle : groupCohomology.IsMulCocycle₁ E.finiteCubicCocycle := by
  intro g h
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective
    (K₁ := X.points.pointField) (AlgebraicClosure ℚ) g
  obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective
    (K₁ := X.points.pointField) (AlgebraicClosure ℚ) h
  rw [← map_mul, E.finiteCubicCocycle_restrict, E.finiteCubicCocycle_restrict,
    E.finiteCubicCocycle_restrict, E.cubicPointCocycle_mul, ofAdd_add,
    map_mul, E.pointFieldMuThreeUnit_smul]

/-- All values of the finite extension cocycle are cube roots of unity. -/
theorem finiteCubicCocycle_cube (g : Gal(X.points.pointField/ℚ)) : E.finiteCubicCocycle g ^ 3 = 1 :=
  E.pointFieldMuThreeUnit_cube _

/-- Hilbert 90 assigns a nonzero rational Kummer parameter to the actual
extension, with an equivariant cube root in its finite Galois point field. -/
theorem exists_actual_cubic_kummer_parameter :
    ∃ a : ℚ, ∃ b : X.points.pointField, a ≠ 0 ∧ b ≠ 0 ∧
      b ^ 3 = algebraMap ℚ X.points.pointField a ∧
      ∀ g : Gal(X.points.pointField/ℚ), g b = (E.finiteCubicCocycle g : X.points.pointField) * b :=
  exists_cubic_kummer_parameter E.finiteCubicCocycle
    E.finiteCubicCocycle_isMulCocycle E.finiteCubicCocycle_cube

end ThreeAdicPlan.FiniteFlatExtension
