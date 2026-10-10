/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveHomogeneousPointTransport
public import FLT.Mazur.ProjectiveLinearOver

/-!
# Homogeneous normalization of the ordered slope markings

The invertible substitution [x₀,x₁] ↦ [a*x₀+x₁,x₁] induces q=v/(v+a).
Its inverse is explicit over any coefficient ring with a unit a.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
namespace FLT.Mazur.ProjectiveLine
open ProjectiveSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (a : Rˣ)

/-- Columns of the homogeneous substitution defining the ordered normalization. -/
def slopeNormalizationMap : (ULift.{u} (Fin 2) →₀ R) →ₗ[R] (ULift.{u} (Fin 2) →₀ R) :=
  Finsupp.linearCombination R
    (fun i => ![(a : R) • Finsupp.single (ULift.up 0) 1 +
      Finsupp.single (ULift.up 1) 1, Finsupp.single (ULift.up 1) 1] i.down)

/-- Columns of the inverse homogeneous substitution. -/
def slopeNormalizationInverse : (ULift.{u} (Fin 2) →₀ R) →ₗ[R] (ULift.{u} (Fin 2) →₀ R) :=
  Finsupp.linearCombination R
    (fun i => ![(↑a⁻¹ : R) • Finsupp.single (ULift.up 0) 1 -
      (↑a⁻¹ : R) • Finsupp.single (ULift.up 1) 1,
      Finsupp.single (ULift.up 1) 1] i.down)

/-- The substitutions are inverse on the entire free module. -/
theorem slopeNormalizationMap_inverse :
    (slopeNormalizationMap a).comp (slopeNormalizationInverse a) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro i r
  rcases i with ⟨i⟩
  fin_cases i <;> ext ⟨j⟩ <;> fin_cases j <;>
    simp [LinearMap.comp_apply, slopeNormalizationMap, slopeNormalizationInverse,
      Finsupp.linearCombination_single, map_sub]

/-- The inverse substitution also cancels in the other order. -/
theorem slopeNormalizationInverse_map :
    (slopeNormalizationInverse a).comp (slopeNormalizationMap a) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro i r
  rcases i with ⟨i⟩
  fin_cases i <;> ext ⟨j⟩ <;> fin_cases j <;>
    simp [LinearMap.comp_apply, slopeNormalizationMap, slopeNormalizationInverse,
      Finsupp.linearCombination_single, map_add, mul_assoc]

/-- The genuine linear equivalence of homogeneous coordinate forms. -/
def slopeNormalizationLinear : (ULift.{u} (Fin 2) →₀ R) ≃ₗ[R] (ULift.{u} (Fin 2) →₀ R) :=
  LinearEquiv.ofLinearMap (slopeNormalizationMap a) (slopeNormalizationInverse a)
    (slopeNormalizationMap_inverse a) (slopeNormalizationInverse_map a)

/-- Its substitution sends X₀ to a*X₀+X₁ and fixes X₁. -/
theorem slopeNormalization_substitution (i : ULift.{u} (Fin 2)) :
    linearSubstitution (slopeNormalizationMap a) (X i) =
      ![C (a : R) * X (ULift.up 0) + X (ULift.up 1), X (ULift.up 1)] i.down := by
  rcases i with ⟨i⟩
  fin_cases i <;> simp [linearSubstitution_X, slopeNormalizationMap,
    Finsupp.linearCombination_single, Algebra.smul_def]

/-- The actual projective automorphism induced by q=v/(v+a). -/
def slopeNormalizationProjIso : space R (ULift.{u} (Fin 2)) ≅ space R (ULift.{u} (Fin 2)) :=
  linearIso (slopeNormalizationLinear a).symm

/-- The homogeneous normalization retains the original coefficient projection. -/
@[reassoc] theorem slopeNormalizationProjIso_base :
    (slopeNormalizationProjIso a).hom ≫ baseProjection R (ULift.{u} (Fin 2)) =
      baseProjection R (ULift.{u} (Fin 2)) :=
  linearIso_baseProjection (slopeNormalizationLinear a).symm

/-- Polynomial evaluation computes the normalization over every affine test ring. -/
theorem slopeNormalization_evaluation {S : Type u} [CommRing S]
    (f : R →+* S) (x : ULift.{u} (Fin 2) → S) :
    (eval₂Hom f x).comp (linearGradedMap (slopeNormalizationLinear a).toLinearMap).toRingHom =
      eval₂Hom f (fun i =>
        ![f a * x (ULift.up 0) + x (ULift.up 1), x (ULift.up 1)] i.down) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [linearGradedMap, linearSubstitution]
  · intro i
    change eval₂Hom f x (linearSubstitution (slopeNormalizationMap a) (X i)) = _
    rw [slopeNormalization_substitution]
    rcases i with ⟨i⟩
    fin_cases i <;> simp

end FLT.Mazur.ProjectiveLine
