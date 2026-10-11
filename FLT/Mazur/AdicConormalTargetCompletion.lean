/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicSquareZeroCompletion
public import FLT.Mazur.AdicModuleIdealTransport

/-!
# Completed conormals over the completed target algebra

For a square-zero presentation, completing its original conormal over the
target algebra gives the conormal of the completed presentation. Surjectivity
of the completed projection upgrades the comparison to completed-target linearity.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicConormalTargetCompletion

open AdicExtensionProjection AdicFormalPresentationHom

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (P : Algebra.Extension.{u} R A) (I : Ideal A)

/-- Restriction to the presenting ring does not change the original conormal completion. -/
def scalarEquiv : AdicCompletion (ideal P I) P.Cotangent ≃ₗ[P.Ring]
    AdicCompletion I P.Cotangent :=
  AdicModuleIdealTransport.equiv (ideal P I) I (ideal_map P I)

/-- The scalar comparison retains the actual completed projection action. -/
theorem scalarEquiv_smul (a : AdicCompletion (ideal P I) P.Ring)
    (x : AdicCompletion (ideal P I) P.Cotangent) :
    scalarEquiv P I (a • x) = projection P I a • scalarEquiv P I x := by
  have he (L J : Ideal A) (h : L = J) (b : AdicCompletion L A) :
      idealEquiv (R := P.Ring) h b = idealEquiv (R := R) h b := by
    subst J
    rfl
  have hh := AdicModuleIdealTransport.equiv_smul (ideal P I) I (ideal_map P I) a x
  change scalarEquiv P I (a • x) = idealEquiv (R := P.Ring) (ideal_map P I)
    (AdicCompletionScalars.algebraMapCompletion (ideal P I) a) • scalarEquiv P I x at hh
  rw [he] at hh
  exact hh

/-- Original conormal elements are preserved under scalar comparison. -/
@[simp] theorem scalarEquiv_of (x : P.Cotangent) :
    scalarEquiv P I (AdicCompletion.of (ideal P I) P.Cotangent x) =
      AdicCompletion.of I P.Cotangent x :=
  AdicModuleIdealTransport.equiv_of (ideal P I) I (ideal_map P I) x

variable [IsNoetherianRing P.Ring]

/-- The scalar action is the actual completed presenting-ring projection. -/
local instance completedAlgebra :
    Algebra (AdicCompletion (ideal P I) P.Ring) (AdicCompletion I A) :=
  (projection P I).toAlgebra

/-- The completed original conormal equals the actual conormal, over the completed target. -/
def equiv (h : P.ker ^ 2 = ⊥) :
    AdicCompletion I P.Cotangent ≃ₗ[AdicCompletion I A] (completed P I).Cotangent where
  __ := (scalarEquiv P I).symm.toAddEquiv.trans
    (AdicSquareZeroCompletion.equiv P I h).toAddEquiv
  map_smul' a x := by
    obtain ⟨a, rfl⟩ := projection_surjective P I a
    obtain ⟨x, rfl⟩ := (scalarEquiv P I).surjective x
    change AdicSquareZeroCompletion.equiv P I h
      ((scalarEquiv P I).symm (projection P I a • scalarEquiv P I x)) = _
    rw [← scalarEquiv_smul, LinearEquiv.symm_apply_apply]
    change AdicSquareZeroCompletion.equiv P I h (a • x) =
      algebraMap (AdicCompletion (ideal P I) P.Ring) (AdicCompletion I A) a •
        AdicSquareZeroCompletion.equiv P I h ((scalarEquiv P I).symm (scalarEquiv P I x))
    rw [LinearEquiv.symm_apply_apply, algebraMap_smul, map_smul]

/-- The target-linear comparison retains original conormal classes. -/
theorem equiv_of_mk (h : P.ker ^ 2 = ⊥) (x : P.ker) :
    equiv P I h (AdicCompletion.of I P.Cotangent (Algebra.Extension.Cotangent.mk x)) =
      Algebra.Extension.Cotangent.mk (AdicSquareZeroCompletion.kernelEquiv P I
        (AdicCompletion.of (ideal P I) P.ker x)) := by
  change AdicSquareZeroCompletion.equiv P I h ((scalarEquiv P I).symm _) = _
  rw [← scalarEquiv_of, LinearEquiv.symm_apply_apply]
  exact AdicSquareZeroCompletion.equiv_of_mk P I h x

end FLT.Mazur.AdicConormalTargetCompletion
