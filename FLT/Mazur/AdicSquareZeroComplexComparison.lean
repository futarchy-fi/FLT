/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicOriginalSpaceProjection
public import FLT.Mazur.AdicConormalTargetCompletion
public import FLT.Mazur.AdicFiniteModuleExt

/-!
# The completed original differential on square-zero presentations

The completed conormal comparison commutes with the original differential,
after projecting formal algebraic differentials to completed originals.
Consequently every formal relation has its genuine original-complex derivative.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicSquareZeroComplexComparison

open AdicExtensionProjection AdicFormalPresentationHom Algebra.Extension

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (P : Algebra.Extension.{u} R A) (I : Ideal A) [IsNoetherianRing P.Ring]
  (h : P.ker ^ 2 = ⊥)

/-- Completing a square-zero presentation commutes with its original conormal differential. -/
theorem chainMap :
    (AdicOriginalSpaceProjection.projection P I).comp
      ((completed P I).cotangentComplex.comp
        (AdicConormalTargetCompletion.equiv P I h).toLinearMap) =
      AdicCompletion.map I P.cotangentComplex := by
  let _ := Cotangent.finite P.ker.fg_of_isNoetherianRing
  apply AdicFiniteModuleExt.ext_of I
  intro x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  change AdicOriginalSpaceProjection.projection P I
    ((completed P I).cotangentComplex
      (AdicConormalTargetCompletion.equiv P I h
        (AdicCompletion.of I P.Cotangent (Cotangent.mk x)))) = _
  rw [AdicConormalTargetCompletion.equiv_of_mk,
    AdicOriginalSpaceProjection.projection_cotangentComplex_mk,
    AdicSquareZeroCompletion.kernelEquiv_val, AdicCompletion.map_of]
  rw [AdicPresentationDerivation.derivation_of, AdicCompletion.map_of, cotangentComplex_mk]
  rfl

/-- The derivative of every completed relation is computed by the completed ORIGINAL complex. -/
theorem derivation_kernel (x : (completed P I).ker) :
    AdicPresentationDerivation.derivation P I x.val =
      AdicCompletion.map I P.cotangentComplex
        ((AdicConormalTargetCompletion.equiv P I h).symm (Cotangent.mk x)) := by
  have he := LinearMap.congr_fun (chainMap P I h)
    ((AdicConormalTargetCompletion.equiv P I h).symm (Cotangent.mk x))
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    AdicOriginalSpaceProjection.projection_cotangentComplex_mk] using he

end FLT.Mazur.AdicSquareZeroComplexComparison
