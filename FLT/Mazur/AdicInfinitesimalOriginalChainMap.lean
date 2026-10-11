/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicSquareZeroFormalChainMap
public import FLT.Mazur.AdicInfinitesimalSpaceMap
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# Infinitesimal formal lifts give chain maps on original complexes

Transport both degrees through infinitesimalization, retaining the genuine
original conormal differentials. The construction applies to different
original algebras related only by their formal target-algebra map.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicInfinitesimalOriginalChainMap

open AdicExtensionProjection

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (P : Algebra.Extension.{u} R A)
  (Q : Algebra.Extension.{u} R B) (I : Ideal A) (J : Ideal B)
  (e : AdicCompletion I A →ₐ[R] AdicCompletion J B)
  (f : AdicCompletion (ideal P.infinitesimal I) P.infinitesimal.Ring →ₐ[R]
    AdicCompletion (ideal Q.infinitesimal J) Q.infinitesimal.Ring)
  (hf : ∀ x, projection Q.infinitesimal J (f x) = e (projection P.infinitesimal I x))
  [IsNoetherianRing P.Ring] [IsNoetherianRing Q.Ring]

/-- The source infinitesimal presenting ring is Noetherian. -/
local instance sourceNoetherian : IsNoetherianRing P.infinitesimal.Ring :=
  inferInstanceAs (IsNoetherianRing (P.Ring ⧸ P.ker ^ 2))

/-- The target infinitesimal presenting ring is Noetherian. -/
local instance targetNoetherian : IsNoetherianRing Q.infinitesimal.Ring :=
  inferInstanceAs (IsNoetherianRing (Q.Ring ⧸ Q.ker ^ 2))

/-- The formal lift gives a semilinear map between the completed original conormals. -/
def conormalMap : AdicCompletion I P.Cotangent →ₛₗ[e.toRingHom]
    AdicCompletion J Q.Cotangent :=
  (AdicCompletion.congr J (InfinitesimalConormalEquiv.equiv Q)).symm.toLinearMap.comp
    ((AdicSquareZeroFormalConormal.map P.infinitesimal Q.infinitesimal I J e f hf
      (InfinitesimalConormalEquiv.ker_square P) (InfinitesimalConormalEquiv.ker_square Q)).comp
        (AdicCompletion.congr I (InfinitesimalConormalEquiv.equiv P)).toLinearMap)

variable [IsNoetherianRing A] [Module.Finite A P.CotangentSpace]

attribute [local instance] AdicInfinitesimalSpaceMap.finiteSpace

/-- Both maps commute with the differential of the completed ORIGINAL cotangent complex. -/
theorem chainMap (x : AdicCompletion I P.Cotangent) :
    AdicInfinitesimalSpaceMap.map P Q I J e f hf
      (AdicCompletion.map I P.cotangentComplex x) =
      AdicCompletion.map J Q.cotangentComplex (conormalMap P Q I J e f hf x) := by
  have hP := LinearMap.congr_fun (AdicInfinitesimalCotangentSpace.chainMap P I) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hP
  change AdicInfinitesimalCotangentSpace.equiv P I
    (AdicCompletion.map I P.cotangentComplex x) = _ at hP
  change (AdicInfinitesimalCotangentSpace.equiv Q J).symm
    (AdicFormalCotangentSpaceMap.map P.infinitesimal Q.infinitesimal I J e f hf
      (AdicInfinitesimalCotangentSpace.equiv P I
        (AdicCompletion.map I P.cotangentComplex x))) = _
  rw [hP, AdicSquareZeroFormalChainMap.chainMap P.infinitesimal Q.infinitesimal I J e f hf
    (InfinitesimalConormalEquiv.ker_square P) (InfinitesimalConormalEquiv.ker_square Q)]
  rw [AdicInfinitesimalCotangentSpace.inverse_chainMap]
  rfl

end FLT.Mazur.AdicInfinitesimalOriginalChainMap
