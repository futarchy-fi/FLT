/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InfinitesimalCotangentSpaceEquiv
public import FLT.Mazur.InfinitesimalConormalEquiv
public import FLT.Mazur.AdicExtensionHomotopy

/-!
# Completed original cotangent complexes and infinitesimalization

Both original degrees are unchanged after completing over the target ideal.
The equivalences commute with the actual completed conormal differential.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicInfinitesimalCotangentSpace

open Algebra.Extension
open scoped TensorProduct

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (P : Algebra.Extension R A) (I : Ideal A)

/-- The original degree-zero comparison extends over the actual completed target. -/
def equiv : AdicCompletion I P.CotangentSpace ≃ₗ[AdicCompletion I A]
    AdicCompletion I P.infinitesimal.CotangentSpace :=
  AdicCompletion.congr I (InfinitesimalCotangentSpaceEquiv.equiv P)

/-- Original cotangent vectors retain the genuine infinitesimal extension map. -/
theorem equiv_of (x : P.CotangentSpace) :
    equiv P I (AdicCompletion.of I P.CotangentSpace x) =
      AdicCompletion.of I P.infinitesimal.CotangentSpace
        (CotangentSpace.map P.toInfinitesimal x) := by
  rw [equiv, AdicCompletion.congr_apply, AdicCompletion.map_of]
  rfl

/-- The equivalence commutes with the completed original conormal differential. -/
theorem chainMap :
    (equiv P I).toLinearMap.comp (AdicCompletion.map I P.cotangentComplex) =
      (AdicCompletion.map I P.infinitesimal.cotangentComplex).comp
        (AdicCompletion.congr I (InfinitesimalConormalEquiv.equiv P)).toLinearMap :=
  AdicExtensionHomotopy.chainMap I P.toInfinitesimal

/-- The reverse comparison also commutes with the completed original differential. -/
theorem inverse_chainMap (x : AdicCompletion I P.infinitesimal.Cotangent) :
    (equiv P I).symm (AdicCompletion.map I P.infinitesimal.cotangentComplex x) =
      AdicCompletion.map I P.cotangentComplex
        ((AdicCompletion.congr I (InfinitesimalConormalEquiv.equiv P)).symm x) := by
  apply (equiv P I).injective
  rw [LinearEquiv.apply_symm_apply]
  have h := LinearMap.congr_fun (chainMap P I)
    ((AdicCompletion.congr I (InfinitesimalConormalEquiv.equiv P)).symm x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using h.symm

end FLT.Mazur.AdicInfinitesimalCotangentSpace
