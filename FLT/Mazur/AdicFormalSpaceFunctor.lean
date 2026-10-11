/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCotangentSemilinearExt
public import FLT.Mazur.AdicFormalSpaceDerivative
public import FLT.Mazur.AdicSquareZeroConormalFunctor

/-!
# Identity and composition for formal original degree-zero maps

Continuous formal lifts act functorially on the completed ORIGINAL
cotangent spaces. Composition uses the proved derivative formula on all
completed sections and the actual containment of target ideals.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicFormalSpaceFunctor

open AdicExtensionProjection
open scoped TensorProduct

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C] (P : Algebra.Extension.{u} R A)
  (Q : Algebra.Extension.{u} R B) (T : Algebra.Extension.{u} R C)
  (I : Ideal A) (J : Ideal B) (K : Ideal C)
  [IsNoetherianRing A] [Module.Finite A P.CotangentSpace]

/-- The identity formal lift acts identically on the completed original degree-zero space. -/
theorem map_id :
    AdicFormalCotangentSpaceMap.map P P I I (AlgHom.id R _) (AlgHom.id R _)
      (fun _ ↦ rfl) = LinearMap.id := by
  apply AdicCotangentSemilinearExt.ext P I
  intro x
  rw [AdicFormalCotangentSpaceMap.map_of_tmul]
  change (1 : AdicCompletion I A) • AdicPresentationDerivation.derivation P I
    (AdicCompletion.of (ideal P I) P.Ring x) = _
  rw [one_smul, AdicPresentationDerivation.derivation_of]
  rfl

variable [IsNoetherianRing B] [Module.Finite B Q.CotangentSpace]
  [IsNoetherianRing Q.Ring]
  (e : AdicCompletion I A →ₐ[R] AdicCompletion J B)
  (d : AdicCompletion J B →ₐ[R] AdicCompletion K C)
  (f : AdicCompletion (ideal P I) P.Ring →ₐ[R] AdicCompletion (ideal Q J) Q.Ring)
  (g : AdicCompletion (ideal Q J) Q.Ring →ₐ[R] AdicCompletion (ideal T K) T.Ring)
  (hf : ∀ x, projection Q J (f x) = e (projection P I x))
  (hg : ∀ x, projection T K (g x) = d (projection Q J x))

/-- Composition of continuous formal lifts composes the completed original space maps. -/
theorem map_comp
    (hd : (J.map (algebraMap B (AdicCompletion J B))).map d.toRingHom ≤
      K.map (algebraMap C (AdicCompletion K C))) :
    AdicFormalCotangentSpaceMap.map P T I K (d.comp e) (g.comp f)
        (AdicSquareZeroConormalFunctor.projection_comp P Q T I J K e d f g hf hg) =
      (AdicFormalCotangentSpaceMap.map Q T J K d g hg).comp
        (AdicFormalCotangentSpaceMap.map P Q I J e f hf) := by
  apply AdicCotangentSemilinearExt.ext P I
  intro x
  change AdicFormalCotangentSpaceMap.map P T I K (d.comp e) (g.comp f) _
    (AdicCompletion.of I P.CotangentSpace (1 ⊗ₜ KaehlerDifferential.D R P.Ring x)) =
      AdicFormalCotangentSpaceMap.map Q T J K d g hg
        (AdicFormalCotangentSpaceMap.map P Q I J e f hf
          (AdicCompletion.of I P.CotangentSpace (1 ⊗ₜ KaehlerDifferential.D R P.Ring x)))
  rw [AdicFormalCotangentSpaceMap.map_of_tmul, AdicFormalCotangentSpaceMap.map_of_tmul]
  change d (e 1) • AdicPresentationDerivation.derivation T K
    (g (f (AdicCompletion.of (ideal P I) P.Ring x))) =
      AdicFormalCotangentSpaceMap.map Q T J K d g hg
        (e 1 • AdicPresentationDerivation.derivation Q J
          (f (AdicCompletion.of (ideal P I) P.Ring x)))
  rw [map_one, map_one, one_smul, one_smul,
    AdicFormalCotangentSpaceMap.map_completed Q T J K d g hg hd]

end FLT.Mazur.AdicFormalSpaceFunctor
