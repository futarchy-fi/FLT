/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantMuThreeKummerCocycle

/-!
# Splitting the prescribed extension from its cubic coboundary

A coboundary for the actual section cocycle corrects the chosen additive
section to an equivariant section. Exactness then supplies the retraction,
retaining the original inclusion and quotient maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ThreeAdicPlan

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- The linear form corresponding to a cube-root point in the chosen coordinates. -/
def muThreeLinearForm (w : muThree.points) : muThree.points →+ ZMod 3 :=
  (AddMonoidHom.mulLeft (muThreeCoordinates.symm w)).comp muThreeCoordinates.symm.toAddMonoidHom

/-- The coordinate generator evaluates to the coefficient of the linear form. -/
theorem muThreeLinearForm_generator (w : muThree.points) :
    muThreeCoordinates (muThreeLinearForm w (muThreeCoordinates 1)) = w := by
  simp [muThreeLinearForm]

/-- Every cube-root point is the corresponding multiple of the coordinate generator. -/
theorem muThreeCoordinates_nsmul (w : muThree.points) :
    w = (muThreeCoordinates.symm w).val • muThreeCoordinates 1 := by
  rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one,
    muThreeCoordinates.apply_symm_apply]

namespace FiniteFlatExtension

variable {X : FiniteFlatObject ZInvTwo} (E : FiniteFlatExtension constantThree X muThree)

/-- A cubic coboundary gives the full Hom-valued coboundary of the extension. -/
theorem sectionDefect_of_cubic_coboundary (w : muThree.points)
    (hw : ∀ σ : Γ, E.cubicPointCocycle σ = σ • w - w) (σ : Γ) (v : muThree.points) :
    E.sectionDefect σ v = muThreeLinearForm w (σ⁻¹ • v) - muThreeLinearForm w v := by
  have hgen : E.sectionDefect σ (muThreeCoordinates 1) =
      muThreeLinearForm w (σ⁻¹ • muThreeCoordinates 1) -
        muThreeLinearForm w (muThreeCoordinates 1) := by
    apply muThreeCoordinates.injective
    rw [map_sub, muThreeCoordinates_contragredient, muThreeLinearForm_generator]
    exact hw σ
  rw [muThreeCoordinates_nsmul v, smul_comm σ⁻¹ (muThreeCoordinates.symm v).val,
    map_nsmul, map_nsmul, map_nsmul, ← nsmul_sub, hgen]

/-- Correct the chosen additive section using a cubic coboundary. -/
def sectionOfCubicCoboundary (w : muThree.points)
    (hw : ∀ σ : Γ, E.cubicPointCocycle σ = σ • w - w) :
    muThree.points →+[Γ] X.points where
  toAddMonoidHom := E.additiveSection -
    (FiniteFlatObject.pointMap E.inclusion).toAddMonoidHom.comp (muThreeLinearForm w)
  map_smul' σ v := by
    change E.additiveSection (σ • v) - FiniteFlatObject.pointMap E.inclusion
      (muThreeLinearForm w (σ • v)) =
      σ • (E.additiveSection v - FiniteFlatObject.pointMap E.inclusion (muThreeLinearForm w v))
    rw [smul_sub]
    have hi (a : constantThree.points) :
        σ • FiniteFlatObject.pointMap E.inclusion a = FiniteFlatObject.pointMap E.inclusion a := by
      rw [← map_smul, constantThree_smul]
    rw [hi]
    have hd := E.sectionDefect_spec σ (σ • v)
    rw [E.sectionDefect_of_cubic_coboundary w hw, inv_smul_smul, map_sub] at hd
    have he := (sub_eq_iff_eq_add).mp hd.symm
    rw [he]
    abel

/-- The corrected section still splits the originally prescribed quotient. -/
theorem sectionOfCubicCoboundary_projection (w : muThree.points)
    (hw : ∀ σ : Γ, E.cubicPointCocycle σ = σ • w - w) (v : muThree.points) :
    FiniteFlatObject.pointMap E.quotient (E.sectionOfCubicCoboundary w hw v) = v := by
  change FiniteFlatObject.pointMap E.quotient
    (E.additiveSection v - FiniteFlatObject.pointMap E.inclusion (muThreeLinearForm w v)) = v
  rw [map_sub, E.additiveSection_projection,
    (E.pointsExact _).mpr ⟨muThreeLinearForm w v, rfl⟩, sub_zero]

/-- Exactness puts the residual of a section in the original kernel. -/
theorem sectionResidual_mem_kernel (s : muThree.points →+[Γ] X.points)
    (hs : ∀ v, FiniteFlatObject.pointMap E.quotient (s v) = v) (x : X.points) :
    ∃ a : constantThree.points, FiniteFlatObject.pointMap E.inclusion a =
      x - s (FiniteFlatObject.pointMap E.quotient x) := by
  apply (E.pointsExact _).mp
  rw [map_sub, hs, sub_self]

/-- The kernel coordinate of the residual is the equivariant retraction. -/
def retractionOfSection (s : muThree.points →+[Γ] X.points)
    (hs : ∀ v, FiniteFlatObject.pointMap E.quotient (s v) = v) :
    X.points →+[Γ] constantThree.points where
  toFun x := (E.sectionResidual_mem_kernel s hs x).choose
  map_zero' := by
    apply E.pointsInjective
    rw [(E.sectionResidual_mem_kernel s hs 0).choose_spec]
    simp
  map_add' x y := by
    apply E.pointsInjective
    rw [(FiniteFlatObject.pointMap E.inclusion).map_add,
      (E.sectionResidual_mem_kernel s hs (x + y)).choose_spec,
      (E.sectionResidual_mem_kernel s hs x).choose_spec,
      (E.sectionResidual_mem_kernel s hs y).choose_spec]
    simp only [map_add]
    abel
  map_smul' σ x := by
    apply E.pointsInjective
    change FiniteFlatObject.pointMap E.inclusion
      (E.sectionResidual_mem_kernel s hs (σ • x)).choose =
      FiniteFlatObject.pointMap E.inclusion (σ • (E.sectionResidual_mem_kernel s hs x).choose)
    rw [(E.sectionResidual_mem_kernel s hs (σ • x)).choose_spec]
    have hi := map_smul (FiniteFlatObject.pointMap E.inclusion) σ
      (E.sectionResidual_mem_kernel s hs x).choose
    rw [hi, (E.sectionResidual_mem_kernel s hs x).choose_spec]
    rw [map_smul, map_smul, smul_sub]

/-- The retraction recovers exactly the residual of the prescribed quotient section. -/
theorem retractionOfSection_spec (s : muThree.points →+[Γ] X.points)
    (hs : ∀ v, FiniteFlatObject.pointMap E.quotient (s v) = v) (x : X.points) :
    FiniteFlatObject.pointMap E.inclusion (E.retractionOfSection s hs x) =
      x - s (FiniteFlatObject.pointMap E.quotient x) :=
  (E.sectionResidual_mem_kernel s hs x).choose_spec

/-- An equivariant section fills the generic split sequence of the actual maps. -/
def genericSplitSequenceOfSection (s : muThree.points →+[Γ] X.points)
    (hs : ∀ v, FiniteFlatObject.pointMap E.quotient (s v) = v) :
    GenericSplitSequence constantThree.toFF X.toFF muThree.toFF where
  inclusion := FiniteFlatObject.pointMap E.inclusion
  retraction := E.retractionOfSection s hs
  projection := FiniteFlatObject.pointMap E.quotient
  sectionMap := s
  retract a := by
    change E.retractionOfSection s hs (FiniteFlatObject.pointMap E.inclusion a) = a
    apply E.pointsInjective
    rw [E.retractionOfSection_spec, (E.pointsExact _).mpr ⟨a, rfl⟩, map_zero, sub_zero]
  sectionProjection := hs
  decomposition x := by
    change FiniteFlatObject.pointMap E.inclusion (E.retractionOfSection s hs x) +
      s (FiniteFlatObject.pointMap E.quotient x) = x
    rw [E.retractionOfSection_spec, sub_add_cancel]

/-- The constructed splitting retains the original generic inclusion. -/
theorem genericSplitSequenceOfSection_inclusion (s : muThree.points →+[Γ] X.points)
    (hs : ∀ v, FiniteFlatObject.pointMap E.quotient (s v) = v) :
    genericHom (X := constantThree.toFF) (Y := X.toFF) E.inclusion =
      (E.genericSplitSequenceOfSection s hs).inclusion := by
  ext a
  rfl

/-- The constructed splitting retains the original generic quotient. -/
theorem genericSplitSequenceOfSection_projection (s : muThree.points →+[Γ] X.points)
    (hs : ∀ v, FiniteFlatObject.pointMap E.quotient (s v) = v) :
    genericHom (X := X.toFF) (Y := muThree.toFF) E.quotient =
      (E.genericSplitSequenceOfSection s hs).projection := by
  ext a
  rfl

/-- A cubic coboundary gives a generic splitting of the prescribed extension. -/
def genericSplitSequenceOfCubicCoboundary (w : muThree.points)
    (hw : ∀ σ : Γ, E.cubicPointCocycle σ = σ • w - w) :
    GenericSplitSequence constantThree.toFF X.toFF muThree.toFF :=
  E.genericSplitSequenceOfSection (E.sectionOfCubicCoboundary w hw)
    (E.sectionOfCubicCoboundary_projection w hw)

/-- A rational cube root of the actual Kummer parameter gives the cubic
coboundary of the original extension cocycle. -/
theorem cubic_coboundary_of_parameter_cube (a : ℚ) (b : X.points.pointField)
    (hb : b ≠ 0) (hpow : b ^ 3 = algebraMap ℚ X.points.pointField a)
    (heq : ∀ g : Gal(X.points.pointField/ℚ),
      g b = (E.finiteCubicCocycle g : X.points.pointField) * b)
    (hr : ∃ r : ℚ, r ^ 3 = a) :
    ∃ w : muThree.points, ∀ σ : Γ, E.cubicPointCocycle σ = σ • w - w := by
  obtain ⟨c, hc, hceq⟩ :=
    (cubic_kummer_parameter_cube_iff E.finiteCubicCocycle a b hb hpow heq).mp hr
  have hc' : (c : AlgebraicClosure ℚ) ^ 3 = 1 := congrArg Subtype.val hc
  obtain ⟨w, hw⟩ := exists_muThreeValue_eq c hc'
  refine ⟨w, fun σ ↦ ?_⟩
  have hσ : σ • w = E.cubicPointCocycle σ + w := by
    apply muThreeValue_injective
    have h := congrArg Subtype.val
      (hceq (AlgEquiv.restrictNormalHom X.points.pointField σ))
    rw [AlgEquiv.restrictNormalHom_apply, E.finiteCubicCocycle_restrict] at h
    have heval := congrArg Units.val (muThreeUnit_smul σ w)
    have hadd := congrArg Units.val (muThreeUnit.map_mul
      (Multiplicative.ofAdd (E.cubicPointCocycle σ)) (Multiplicative.ofAdd w))
    change muThreeValue (σ • w) = σ (muThreeValue w) at heval
    change muThreeValue (E.cubicPointCocycle σ + w) =
      muThreeValue (E.cubicPointCocycle σ) * muThreeValue w at hadd
    rw [heval, hadd, hw]
    exact h
  exact (eq_sub_iff_add_eq).mpr hσ.symm

/-- Cubeness of the actual Kummer parameter fills the generic split sequence,
including identification with both prescribed maps. -/
theorem exists_genericSplitSequence_of_parameter_cube (a : ℚ) (b : X.points.pointField)
    (hb : b ≠ 0) (hpow : b ^ 3 = algebraMap ℚ X.points.pointField a)
    (heq : ∀ g : Gal(X.points.pointField/ℚ),
      g b = (E.finiteCubicCocycle g : X.points.pointField) * b)
    (hr : ∃ r : ℚ, r ^ 3 = a) :
    ∃ s : GenericSplitSequence constantThree.toFF X.toFF muThree.toFF,
      genericHom (X := constantThree.toFF) (Y := X.toFF) E.inclusion = s.inclusion ∧
      genericHom (X := X.toFF) (Y := muThree.toFF) E.quotient = s.projection := by
  obtain ⟨w, hw⟩ := E.cubic_coboundary_of_parameter_cube a b hb hpow heq hr
  exact ⟨E.genericSplitSequenceOfCubicCoboundary w hw,
    E.genericSplitSequenceOfSection_inclusion _ _, E.genericSplitSequenceOfSection_projection _ _⟩

end FiniteFlatExtension
end ThreeAdicPlan
