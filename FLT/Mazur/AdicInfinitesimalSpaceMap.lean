/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicFormalCotangentSpaceMap
public import FLT.Mazur.AdicInfinitesimalCotangentSpace

/-!
# Formal infinitesimal lifts act on original degree-zero spaces

Transport the genuine formal cotangent map through the proved invariance
under infinitesimalization. Both source and target retain their ORIGINAL
presentations, tensor differential modules, and completed target actions.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicInfinitesimalSpaceMap

open AdicExtensionProjection
open scoped TensorProduct

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (P : Algebra.Extension.{u} R A)
  (Q : Algebra.Extension.{u} R B) (I : Ideal A) (J : Ideal B)
  (e : AdicCompletion I A →ₐ[R] AdicCompletion J B)
  (f : AdicCompletion (ideal P.infinitesimal I) P.infinitesimal.Ring →ₐ[R]
    AdicCompletion (ideal Q.infinitesimal J) Q.infinitesimal.Ring)
  (hf : ∀ x, projection Q.infinitesimal J (f x) = e (projection P.infinitesimal I x))
  [IsNoetherianRing A] [Module.Finite A P.CotangentSpace]

/-- Infinitesimalization preserves finiteness of the original degree-zero space. -/
local instance finiteSpace : Module.Finite A P.infinitesimal.CotangentSpace :=
  Module.Finite.of_surjective (InfinitesimalCotangentSpaceEquiv.equiv P).toLinearMap
    (InfinitesimalCotangentSpaceEquiv.equiv P).surjective

/-- The constructed map acts between completed ORIGINAL presentation cotangent spaces. -/
def map : AdicCompletion I P.CotangentSpace →ₛₗ[e.toRingHom]
    AdicCompletion J Q.CotangentSpace :=
  (AdicInfinitesimalCotangentSpace.equiv Q J).symm.toLinearMap.comp
    ((AdicFormalCotangentSpaceMap.map P.infinitesimal Q.infinitesimal I J e f hf).comp
      (AdicInfinitesimalCotangentSpace.equiv P I).toLinearMap)

/-- Its original tensor values are derivatives of the actual infinitesimal formal lift. -/
theorem map_of_tmul (a : A) (x : P.Ring) :
    map P Q I J e f hf (AdicCompletion.of I P.CotangentSpace
      (a ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x)) =
        e (AdicCompletion.of I A a) • (AdicInfinitesimalCotangentSpace.equiv Q J).symm
          (AdicPresentationDerivation.derivation Q.infinitesimal J
            (f (AdicCompletion.of (ideal P.infinitesimal I) P.infinitesimal.Ring
              (P.toInfinitesimal.toAlgHom x)))) := by
  change (AdicInfinitesimalCotangentSpace.equiv Q J).symm
    (AdicFormalCotangentSpaceMap.map P.infinitesimal Q.infinitesimal I J e f hf
      (AdicInfinitesimalCotangentSpace.equiv P I
        (AdicCompletion.of I P.CotangentSpace _))) = _
  rw [AdicInfinitesimalCotangentSpace.equiv_of, Algebra.Extension.CotangentSpace.map_tmul]
  rw [AdicFormalCotangentSpaceMap.map_of_tmul, map_smul]
  rfl

end FLT.Mazur.AdicInfinitesimalSpaceMap
