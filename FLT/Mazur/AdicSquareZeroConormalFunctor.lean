/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicSquareZeroFormalConormal

/-!
# Functoriality of formal maps on completed original conormals

Identity and composition laws are proved using arbitrary actual completed
relations. No inverse property of the chosen formal lifts is assumed.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicSquareZeroConormalFunctor

open AdicExtensionProjection AdicFormalPresentationHom Algebra.Extension

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C] (P : Algebra.Extension.{u} R A)
  (Q : Algebra.Extension.{u} R B) (T : Algebra.Extension.{u} R C)
  (I : Ideal A) (J : Ideal B) (K : Ideal C)
  (e : AdicCompletion I A →ₐ[R] AdicCompletion J B)
  (d : AdicCompletion J B →ₐ[R] AdicCompletion K C)
  (f : AdicCompletion (ideal P I) P.Ring →ₐ[R] AdicCompletion (ideal Q J) Q.Ring)
  (g : AdicCompletion (ideal Q J) Q.Ring →ₐ[R] AdicCompletion (ideal T K) T.Ring)
  (hf : ∀ x, projection Q J (f x) = e (projection P I x))
  (hg : ∀ x, projection T K (g x) = d (projection Q J x))
  [IsNoetherianRing P.Ring] [IsNoetherianRing Q.Ring] [IsNoetherianRing T.Ring]
  (hP : P.ker ^ 2 = ⊥) (hQ : Q.ker ^ 2 = ⊥) (hT : T.ker ^ 2 = ⊥)

/-- Formal conormal maps preserve the representative of every completed relation. -/
theorem map_equiv_symm_mk (x : (completed P I).ker) :
    AdicSquareZeroFormalConormal.map P Q I J e f hf hP hQ
        ((AdicConormalTargetCompletion.equiv P I hP).symm (Cotangent.mk x)) =
      (AdicConormalTargetCompletion.equiv Q J hQ).symm
        (Cotangent.mk (AdicSquareZeroFormalConormal.kernelMap P Q I J e f hf x)) := by
  let _ := e.toAlgebra
  change (AdicConormalTargetCompletion.equiv Q J hQ).symm
    (Cotangent.map (AdicSquareZeroFormalConormal.hom P Q I J e f hf)
      (AdicConormalTargetCompletion.equiv P I hP
        ((AdicConormalTargetCompletion.equiv P I hP).symm (Cotangent.mk x)))) = _
  rw [LinearEquiv.apply_symm_apply, Cotangent.map_mk]
  rfl

/-- The identity formal lift acts identically on completed original conormals. -/
theorem map_id (x : AdicCompletion I P.Cotangent) :
    AdicSquareZeroFormalConormal.map P P I I (AlgHom.id R _) (AlgHom.id R _)
      (fun _ ↦ rfl) hP hP x = x := by
  obtain ⟨x, rfl⟩ := (AdicConormalTargetCompletion.equiv P I hP).symm.surjective x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  rw [map_equiv_symm_mk]
  rfl

include hf hg in
omit [IsNoetherianRing P.Ring] [IsNoetherianRing Q.Ring] [IsNoetherianRing T.Ring] in
/-- Composing lifts commutes with the actual completed target projections. -/
theorem projection_comp (x : AdicCompletion (ideal P I) P.Ring) :
    projection T K ((g.comp f) x) = (d.comp e) (projection P I x) := by
  change projection T K (g (f x)) = d (e (projection P I x))
  rw [hg, hf]

/-- Composing formal lifts composes the completed ORIGINAL conormal maps. -/
theorem map_comp (x : AdicCompletion I P.Cotangent) :
    AdicSquareZeroFormalConormal.map P T I K (d.comp e) (g.comp f)
        (projection_comp P Q T I J K e d f g hf hg) hP hT x =
      AdicSquareZeroFormalConormal.map Q T J K d g hg hQ hT
        (AdicSquareZeroFormalConormal.map P Q I J e f hf hP hQ x) := by
  obtain ⟨x, rfl⟩ := (AdicConormalTargetCompletion.equiv P I hP).symm.surjective x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  rw [map_equiv_symm_mk, map_equiv_symm_mk, map_equiv_symm_mk]
  rfl

end FLT.Mazur.AdicSquareZeroConormalFunctor
