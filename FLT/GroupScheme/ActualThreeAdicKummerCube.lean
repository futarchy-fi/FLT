/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantMuThreeKummerCocycle
public import FLT.GroupScheme.PadicActualConstantMuThreeSection
public import FLT.GroupScheme.RestrictedScalarPointNaturality

/-!
# The actual extension's Kummer parameter is a three-adic cube

The section on the original three-adic model becomes an equivariant section
of the restricted original point module. Comparing it with the chosen rational
additive section gives a local cubic coboundary. Dividing the Kummer cube root
by this root of unity yields a Galois-fixed element, hence an element of `ℚ₃`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ThreeAdicPlan.FiniteFlatExtension

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ
local notation "Γ₃" => AlgebraicClosure ℚ_[3] ≃ₐ[ℚ_[3]] AlgebraicClosure ℚ_[3]
local notation "ρ₃" => Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[3])

/-- Three does not divide the inverted denominator. -/
local instance notThreeDvdTwo : Fact (¬ (3 : ℤ) ∣ 2) := ⟨by norm_num⟩

variable {X : FiniteFlatObject ZInvTwo} (E : FiniteFlatExtension constantThree X muThree)

/-- The section of the actual local model splits the restricted original point quotient. -/
theorem exists_actual_three_adic_pointSection :
    ∃ t : muThree.points →+ X.points,
      (∀ w, FiniteFlatObject.pointMap E.quotient (t w) = w) ∧
      ∀ (σ : Γ₃) (w : muThree.points), t (ρ₃ σ • w) = ρ₃ σ • t w := by
  obtain ⟨s, hs⟩ := E.exists_actual_three_adic_section
  let s' : ModelHom (muThree.toFF.restrictedScalarExtension ℤ_[3] ℚ_[3])
      (X.toFF.restrictedScalarExtension ℤ_[3] ℚ_[3]) := s
  let t := genericHom s'
  refine ⟨t.toAddMonoidHom, ?_, fun σ w ↦ t.map_smul σ w⟩
  intro w
  have hs' : s'.comp (Bialgebra.TensorProduct.map (BialgHom.id ℤ_[3] ℤ_[3]) E.quotient) =
      BialgHom.id ℤ_[3] (muThree.toFF.restrictedScalarExtension ℤ_[3] ℚ_[3]).CoordinateRing := hs
  have h := congrArg (fun f : ModelHom (muThree.toFF.restrictedScalarExtension ℤ_[3] ℚ_[3])
      (muThree.toFF.restrictedScalarExtension ℤ_[3] ℚ_[3]) ↦ genericHom f w) hs'
  rw [genericHom_comp, genericHom_id,
    ModelHom.genericHom_restrictedScalarExtension ℤ_[3] ℚ_[3]
      (X := X.toFF) (Y := muThree.toFF) E.quotient] at h
  exact h

/-- The difference of two additive quotient sections lies in the prescribed kernel. -/
theorem sectionComparison_mem_kernel (t : muThree.points →+ X.points)
    (ht : ∀ w, FiniteFlatObject.pointMap E.quotient (t w) = w) (w : muThree.points) :
    ∃ a : constantThree.points,
      FiniteFlatObject.pointMap E.inclusion a = E.additiveSection w - t w := by
  apply (E.pointsExact _).mp
  rw [map_sub, E.additiveSection_projection, ht, sub_self]

/-- The additive kernel coordinate of the difference between two quotient sections. -/
def sectionComparison (t : muThree.points →+ X.points)
    (ht : ∀ w, FiniteFlatObject.pointMap E.quotient (t w) = w) :
    muThree.points →+ constantThree.points where
  toFun w := (E.sectionComparison_mem_kernel t ht w).choose
  map_zero' := by
    apply E.pointsInjective
    rw [(E.sectionComparison_mem_kernel t ht 0).choose_spec]
    simp
  map_add' w v := by
    apply E.pointsInjective
    rw [(FiniteFlatObject.pointMap E.inclusion).map_add,
      (E.sectionComparison_mem_kernel t ht (w + v)).choose_spec,
      (E.sectionComparison_mem_kernel t ht w).choose_spec,
      (E.sectionComparison_mem_kernel t ht v).choose_spec]
    simp only [map_add]
    abel

/-- Inclusion recovers the actual difference of the two sections. -/
theorem sectionComparison_spec (t : muThree.points →+ X.points)
    (ht : ∀ w, FiniteFlatObject.pointMap E.quotient (t w) = w) (w : muThree.points) :
    FiniteFlatObject.pointMap E.inclusion (E.sectionComparison t ht w) =
      E.additiveSection w - t w :=
  (E.sectionComparison_mem_kernel t ht w).choose_spec

/-- The actual extension's cubic cocycle is a coboundary on the three-adic Galois group. -/
theorem exists_actual_three_adic_cubic_coboundary :
    ∃ w : muThree.points, ∀ σ : Γ₃, E.cubicPointCocycle (ρ₃ σ) = ρ₃ σ • w - w := by
  obtain ⟨t, ht, hteq⟩ := E.exists_actual_three_adic_pointSection
  let d := E.sectionComparison t ht
  have hd (σ : Γ₃) (v : muThree.points) :
      E.sectionDefect (ρ₃ σ) v = d ((ρ₃ σ)⁻¹ • v) - d v := by
    apply E.pointsInjective
    rw [E.sectionDefect_spec, map_sub]
    have h := congrArg (fun x : X.points ↦ ρ₃ σ • x)
      (E.sectionComparison_spec t ht ((ρ₃ σ)⁻¹ • v))
    rw [← map_smul, constantThree_smul] at h
    rw [h, E.sectionComparison_spec, smul_sub, ← hteq, smul_inv_smul]
    abel
  refine ⟨muThreeCoordinates (d (muThreeCoordinates 1)), fun σ ↦ ?_⟩
  unfold cubicPointCocycle
  rw [hd, map_sub]
  exact congrArg (fun z : muThree.points ↦ z - muThreeCoordinates (d (muThreeCoordinates 1)))
    (muThreeCoordinates_contragredient (ρ₃ σ) d)

/-- A Kummer cube root in the actual point field descends to a cube root over `ℚ₃`. -/
theorem actual_cubic_kummer_parameter_three_adic_cube (a : ℚ) (b : X.points.pointField)
    (hpow : b ^ 3 = algebraMap ℚ X.points.pointField a)
    (heq : ∀ g : Gal(X.points.pointField/ℚ),
      g b = (E.finiteCubicCocycle g : X.points.pointField) * b) :
    ∃ r : ℚ_[3], r ^ 3 = (a : ℚ_[3]) := by
  obtain ⟨w, hw⟩ := E.exists_actual_three_adic_cubic_coboundary
  let j := AlgebraicClosure.map (algebraMap ℚ ℚ_[3])
  let c := j (muThreeValue w)
  have hc : c ^ 3 = 1 := by rw [← map_pow, muThreeValue_cube, map_one]
  have hbσ (σ : Γ₃) :
      ρ₃ σ (b : AlgebraicClosure ℚ) =
        muThreeValue (E.cubicPointCocycle (ρ₃ σ)) * (b : AlgebraicClosure ℚ) := by
    have h := congrArg Subtype.val (heq (AlgEquiv.restrictNormalHom X.points.pointField (ρ₃ σ)))
    rw [AlgEquiv.restrictNormalHom_apply, E.finiteCubicCocycle_restrict] at h
    exact h
  have hwσ (σ : Γ₃) :
      ρ₃ σ (muThreeValue w) = muThreeValue (E.cubicPointCocycle (ρ₃ σ)) * muThreeValue w := by
    have h := congrArg Units.val (muThreeUnit_smul (ρ₃ σ) w)
    change muThreeValue (ρ₃ σ • w) = ρ₃ σ (muThreeValue w) at h
    rw [← h, ← sub_add_cancel (ρ₃ σ • w) w, ← hw σ]
    exact congrArg Units.val (muThreeUnit.map_mul
      (Multiplicative.ofAdd (E.cubicPointCocycle (ρ₃ σ))) (Multiplicative.ofAdd w))
  have hfixed (σ : Γ₃) : σ (j (b : AlgebraicClosure ℚ) / c) = j (b : AlgebraicClosure ℚ) / c := by
    change σ (j (b : AlgebraicClosure ℚ) / j (muThreeValue w)) =
      j (b : AlgebraicClosure ℚ) / j (muThreeValue w)
    rw [map_div₀, ← Field.absoluteGaloisGroup.lift_map, ← Field.absoluteGaloisGroup.lift_map,
      hbσ, hwσ, map_mul, map_mul]
    exact mul_div_mul_left _ _ ((map_ne_zero j).mpr (muThreeValue_ne_zero _))
  obtain ⟨r, hr⟩ :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (j (b : AlgebraicClosure ℚ) / c)).mpr hfixed
  refine ⟨r, (algebraMap ℚ_[3] (AlgebraicClosure ℚ_[3])).injective ?_⟩
  rw [map_pow, hr, div_pow, hc, div_one]
  have hbpow : (b : AlgebraicClosure ℚ) ^ 3 = algebraMap ℚ (AlgebraicClosure ℚ) a :=
    congrArg Subtype.val hpow
  rw [← map_pow, hbpow, AlgebraicClosure.map_algebraMap]
  simp

end ThreeAdicPlan.FiniteFlatExtension
