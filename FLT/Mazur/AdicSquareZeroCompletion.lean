/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicSquareZeroConormal

/-!
# Completing the original conormal of a square-zero extension

Exactness identifies the completed original kernel with the kernel of the
completed projection. For a square-zero extension this also identifies the
completed original conormal, retaining its presenting-ring scalar action.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicSquareZeroCompletion

open AdicExtensionProjection AdicFormalPresentationHom

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (P : Algebra.Extension.{u} R A) (I : Ideal A) [IsNoetherianRing P.Ring]

/-- Complete the inclusion of the original kernel into the actual completed kernel. -/
def kernelMap : AdicCompletion (ideal P I) P.ker →ₗ[
    AdicCompletion (ideal P I) P.Ring] (completed P I).ker :=
  (AdicCompletion.map (ideal P I) P.ker.subtype).codRestrict _ fun x ↦ by
    change projection P I (AdicCompletion.map (ideal P I) P.ker.subtype x) = 0
    rw [projection_eq_zero_iff, ← LinearMap.comp_apply, AdicCompletion.map_comp]
    have hz : (Algebra.linearMap P.Ring A).comp P.ker.subtype = 0 := by
      ext y
      exact y.property
    rw [hz, AdicCompletion.map_zero, LinearMap.zero_apply]

/-- Completion gives precisely the kernel of the actual completed projection. -/
def kernelEquiv : AdicCompletion (ideal P I) P.ker ≃ₗ[
    AdicCompletion (ideal P I) P.Ring] (completed P I).ker :=
  LinearEquiv.ofBijective (kernelMap P I) ⟨by
    intro x y h
    exact AdicCompletion.map_injective (ideal P I) (Submodule.injective_subtype _)
      (congrArg Subtype.val h), by
    intro y
    have hy : y.val ∈ P.ker.map
        (algebraMap P.Ring (AdicCompletion (ideal P I) P.Ring)) := by
      rw [← ker_projection P I]
      exact y.property
    rw [← AdicIdealCompletionRange.range_map_subtype] at hy
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩⟩

/-- The kernel equivalence is the completed original inclusion. -/
@[simp] theorem kernelEquiv_val (x : AdicCompletion (ideal P I) P.ker) :
    (kernelEquiv P I x).val = AdicCompletion.map (ideal P I) P.ker.subtype x := rfl

/-- A square-zero presentation's original conormal is its original kernel. -/
def originalEquiv (h : P.ker ^ 2 = ⊥) : P.Cotangent ≃ₗ[P.Ring] P.ker :=
  P.cotangentEquivCotangentKer ≪≫ₗ (AdicSquareZeroConormal.idealEquiv P.ker h).symm

omit [IsNoetherianRing P.Ring] in
/-- The original conormal identification retains each kernel representative. -/
@[simp] theorem originalEquiv_mk (h : P.ker ^ 2 = ⊥) (x : P.ker) :
    originalEquiv P h (Algebra.Extension.Cotangent.mk x) = x :=
  (AdicSquareZeroConormal.idealEquiv P.ker h).symm_apply_apply x

/-- The actual completed projection supplies the presenting-ring action. -/
local instance completedAlgebra :
    Algebra (AdicCompletion (ideal P I) P.Ring) (AdicCompletion I A) :=
  (projection P I).toAlgebra

/-- Completing the original conormal recovers the completed extension's conormal. -/
def equiv (h : P.ker ^ 2 = ⊥) :
    AdicCompletion (ideal P I) P.Cotangent ≃ₗ[AdicCompletion (ideal P I) P.Ring]
      (completed P I).Cotangent :=
  AdicCompletion.congr (ideal P I) (originalEquiv P h) ≪≫ₗ kernelEquiv P I ≪≫ₗ
    (AdicSquareZeroConormal.completedEquiv P I h).symm

/-- On original conormal classes the comparison uses the original kernel inclusion. -/
theorem equiv_of_mk (h : P.ker ^ 2 = ⊥) (x : P.ker) :
    equiv P I h (AdicCompletion.of (ideal P I) P.Cotangent
      (Algebra.Extension.Cotangent.mk x)) =
        Algebra.Extension.Cotangent.mk
          (kernelEquiv P I (AdicCompletion.of (ideal P I) P.ker x)) := by
  apply (AdicSquareZeroConormal.completedEquiv P I h).injective
  change AdicSquareZeroConormal.completedEquiv P I h
    ((AdicSquareZeroConormal.completedEquiv P I h).symm
      (kernelEquiv P I (AdicCompletion.congr (ideal P I) (originalEquiv P h)
        (AdicCompletion.of (ideal P I) P.Cotangent
          (Algebra.Extension.Cotangent.mk x))))) = _
  rw [LinearEquiv.apply_symm_apply, AdicCompletion.congr_apply, AdicCompletion.map_of]
  simp only [LinearEquiv.coe_coe, originalEquiv_mk,
    AdicSquareZeroConormal.completedEquiv_mk]

end FLT.Mazur.AdicSquareZeroCompletion
