/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicFormalSpaceFunctor
public import FLT.Mazur.AdicInfinitesimalOriginalChainMap

/-!
# Functoriality on original cotangent spaces under formal infinitesimal lifts

Both identity and composition survive transport to the original completed
cotangent spaces. The formal lifts need not themselves be inverse maps.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicInfinitesimalSpaceFunctor

open AdicExtensionProjection

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C] (P : Algebra.Extension.{u} R A)
  (Q : Algebra.Extension.{u} R B) (T : Algebra.Extension.{u} R C)
  (I : Ideal A) (J : Ideal B) (K : Ideal C)
  [IsNoetherianRing A] [Module.Finite A P.CotangentSpace]

attribute [local instance] AdicInfinitesimalSpaceMap.finiteSpace
  AdicInfinitesimalOriginalChainMap.sourceNoetherian

/-- The infinitesimal identity fixes completed original cotangent spaces. -/
theorem map_id (x : AdicCompletion I P.CotangentSpace) :
    AdicInfinitesimalSpaceMap.map P P I I (AlgHom.id R _) (AlgHom.id R _)
      (fun _ ↦ rfl) x = x := by
  change (AdicInfinitesimalCotangentSpace.equiv P I).symm
    (AdicFormalCotangentSpaceMap.map P.infinitesimal P.infinitesimal I I
      (AlgHom.id R _) (AlgHom.id R _) _
        (AdicInfinitesimalCotangentSpace.equiv P I x)) = x
  rw [AdicFormalSpaceFunctor.map_id, LinearMap.id_apply, LinearEquiv.symm_apply_apply]

variable [IsNoetherianRing B] [Module.Finite B Q.CotangentSpace]
  [IsNoetherianRing Q.Ring]
  (e : AdicCompletion I A →ₐ[R] AdicCompletion J B)
  (d : AdicCompletion J B →ₐ[R] AdicCompletion K C)
  (f : AdicCompletion (ideal P.infinitesimal I) P.infinitesimal.Ring →ₐ[R]
    AdicCompletion (ideal Q.infinitesimal J) Q.infinitesimal.Ring)
  (g : AdicCompletion (ideal Q.infinitesimal J) Q.infinitesimal.Ring →ₐ[R]
    AdicCompletion (ideal T.infinitesimal K) T.infinitesimal.Ring)
  (hf : ∀ x, projection Q.infinitesimal J (f x) = e (projection P.infinitesimal I x))
  (hg : ∀ x, projection T.infinitesimal K (g x) = d (projection Q.infinitesimal J x))

/-- Composed infinitesimal formal lifts give composed original space maps. -/
theorem map_comp
    (hd : (J.map (algebraMap B (AdicCompletion J B))).map d.toRingHom ≤
      K.map (algebraMap C (AdicCompletion K C)))
    (x : AdicCompletion I P.CotangentSpace) :
    AdicInfinitesimalSpaceMap.map P T I K (d.comp e) (g.comp f)
        (AdicSquareZeroConormalFunctor.projection_comp P.infinitesimal Q.infinitesimal
          T.infinitesimal I J K e d f g hf hg) x =
      AdicInfinitesimalSpaceMap.map Q T J K d g hg
        (AdicInfinitesimalSpaceMap.map P Q I J e f hf x) := by
  simp only [AdicInfinitesimalSpaceMap.map, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [AdicFormalSpaceFunctor.map_comp P.infinitesimal Q.infinitesimal T.infinitesimal
    I J K e d f g hf hg hd]
  rfl

end FLT.Mazur.AdicInfinitesimalSpaceFunctor
