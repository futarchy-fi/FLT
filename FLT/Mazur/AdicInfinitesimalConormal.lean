/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicConormalTargetCompletion
public import FLT.Mazur.InfinitesimalConormalEquiv
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# The original conormal inside a completed infinitesimal presentation

The conormal of the completed infinitesimal presentation is the completion
of the original presentation's conormal, linearly over the completed target.
This statement makes no claim about algebraic differentials of completed rings.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicInfinitesimalConormal

open AdicExtensionProjection AdicFormalPresentationHom Algebra.Extension

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (P : Algebra.Extension.{u} R A) (I : Ideal A) [IsNoetherianRing P.Ring]

/-- The original infinitesimal presenting ring is still Noetherian. -/
local instance infinitesimalNoetherian : IsNoetherianRing P.infinitesimal.Ring :=
  inferInstanceAs (IsNoetherianRing (P.Ring ⧸ P.ker ^ 2))

/-- The completed infinitesimal conormal is the completed original conormal over its target. -/
def equiv : AdicCompletion I P.Cotangent ≃ₗ[AdicCompletion I A]
    (completed P.infinitesimal I).Cotangent :=
  AdicCompletion.congr I (InfinitesimalConormalEquiv.equiv P) ≪≫ₗ
    AdicConormalTargetCompletion.equiv P.infinitesimal I
      (InfinitesimalConormalEquiv.ker_square P)

/-- On original elements the comparison uses the genuine infinitesimal extension map. -/
theorem equiv_of (x : P.Cotangent) :
    equiv P I (AdicCompletion.of I P.Cotangent x) =
      AdicConormalTargetCompletion.equiv P.infinitesimal I
        (InfinitesimalConormalEquiv.ker_square P)
        (AdicCompletion.of I P.infinitesimal.Cotangent
          (Cotangent.map P.toInfinitesimal x)) := by
  change AdicConormalTargetCompletion.equiv P.infinitesimal I _
    (AdicCompletion.congr I (InfinitesimalConormalEquiv.equiv P)
      (AdicCompletion.of I P.Cotangent x)) = _
  rw [AdicCompletion.congr_apply, AdicCompletion.map_of]
  rfl

/-- Every completed original relation class retains its actual infinitesimal representative. -/
theorem equiv_of_mk (x : P.ker) :
    equiv P I (AdicCompletion.of I P.Cotangent (Cotangent.mk x)) =
      Cotangent.mk (AdicSquareZeroCompletion.kernelEquiv P.infinitesimal I
        (AdicCompletion.of (ideal P.infinitesimal I) P.infinitesimal.ker
          ⟨P.toInfinitesimal.toAlgHom x, by
            change algebraMap P.Ring A x.val = 0
            exact x.property⟩)) := by
  rw [equiv_of, Cotangent.map_mk]
  exact AdicConormalTargetCompletion.equiv_of_mk P.infinitesimal I
    (InfinitesimalConormalEquiv.ker_square P) _

end FLT.Mazur.AdicInfinitesimalConormal
