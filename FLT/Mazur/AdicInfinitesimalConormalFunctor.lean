/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicSquareZeroConormalFunctor
public import FLT.Mazur.AdicInfinitesimalOriginalChainMap

/-!
# Functoriality on original conormals under formal infinitesimal lifts

Both identity and composition survive transport to the original completed
conormal modules. The formal lifts need not themselves be inverse maps.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicInfinitesimalConormalFunctor

open AdicExtensionProjection

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C] (P : Algebra.Extension.{u} R A)
  (Q : Algebra.Extension.{u} R B) (T : Algebra.Extension.{u} R C)
  (I : Ideal A) (J : Ideal B) (K : Ideal C)
  [IsNoetherianRing P.Ring] [IsNoetherianRing Q.Ring] [IsNoetherianRing T.Ring]

attribute [local instance] AdicInfinitesimalOriginalChainMap.sourceNoetherian
  AdicInfinitesimalOriginalChainMap.targetNoetherian

/-- The formal infinitesimal identity induces the identity on completed original conormals. -/
theorem map_id (x : AdicCompletion I P.Cotangent) :
    AdicInfinitesimalOriginalChainMap.conormalMap P P I I (AlgHom.id R _) (AlgHom.id R _)
      (fun _ ↦ rfl) x = x := by
  change (AdicCompletion.congr I (InfinitesimalConormalEquiv.equiv P)).symm
    (AdicSquareZeroFormalConormal.map P.infinitesimal P.infinitesimal I I
      (AlgHom.id R _) (AlgHom.id R _) _ _ _
        (AdicCompletion.congr I (InfinitesimalConormalEquiv.equiv P) x)) = x
  rw [AdicSquareZeroConormalFunctor.map_id, LinearEquiv.symm_apply_apply]

variable (e : AdicCompletion I A →ₐ[R] AdicCompletion J B)
  (d : AdicCompletion J B →ₐ[R] AdicCompletion K C)
  (f : AdicCompletion (ideal P.infinitesimal I) P.infinitesimal.Ring →ₐ[R]
    AdicCompletion (ideal Q.infinitesimal J) Q.infinitesimal.Ring)
  (g : AdicCompletion (ideal Q.infinitesimal J) Q.infinitesimal.Ring →ₐ[R]
    AdicCompletion (ideal T.infinitesimal K) T.infinitesimal.Ring)
  (hf : ∀ x, projection Q.infinitesimal J (f x) = e (projection P.infinitesimal I x))
  (hg : ∀ x, projection T.infinitesimal K (g x) = d (projection Q.infinitesimal J x))

/-- Composed infinitesimal formal lifts give composed original conormal maps. -/
theorem map_comp (x : AdicCompletion I P.Cotangent) :
    AdicInfinitesimalOriginalChainMap.conormalMap P T I K (d.comp e) (g.comp f)
        (AdicSquareZeroConormalFunctor.projection_comp P.infinitesimal Q.infinitesimal
          T.infinitesimal I J K e d f g hf hg) x =
      AdicInfinitesimalOriginalChainMap.conormalMap Q T J K d g hg
        (AdicInfinitesimalOriginalChainMap.conormalMap P Q I J e f hf x) := by
  simp only [AdicInfinitesimalOriginalChainMap.conormalMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [AdicSquareZeroConormalFunctor.map_comp P.infinitesimal Q.infinitesimal T.infinitesimal
    I J K e d f g hf hg (InfinitesimalConormalEquiv.ker_square P)
    (InfinitesimalConormalEquiv.ker_square Q) (InfinitesimalConormalEquiv.ker_square T)]

end FLT.Mazur.AdicInfinitesimalConormalFunctor
