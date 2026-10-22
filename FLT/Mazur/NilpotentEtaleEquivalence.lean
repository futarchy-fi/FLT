/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Etale.Basic

/-!
# Lifting equivalences of etale algebras across nilpotent ideals

A specified equivalence of the reductions lifts to a unique equivalence of
formally etale algebras. Both inverse identities are proved using infinitesimal
uniqueness; no inverse or compatibility data are assumed before lifting.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NilpotentEtale
variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra.FormallyEtale R A]
  (I : Ideal A) (J : Ideal B) (hI : IsNilpotent I) (hJ : IsNilpotent J)
  (e : (A ⧸ I) ≃ₐ[R] (B ⧸ J))

/-- Lift the specified reduced coefficient comparison. -/
def liftHom : A →ₐ[R] B :=
  Algebra.FormallySmooth.lift J hJ (e.toAlgHom.comp (Ideal.Quotient.mkₐ R I))

/-- The lifted comparison retains exactly the original reduction. -/
theorem liftHom_reduction (a : A) :
    Ideal.Quotient.mk J (liftHom I J hJ e a) = e (Ideal.Quotient.mk I a) :=
  Algebra.FormallySmooth.mk_lift J hJ _ a

/-- The specified infinitesimal comparison has only one lift. -/
theorem liftHom_unique (f : A →ₐ[R] B)
    (hf : ∀ a, Ideal.Quotient.mk J (f a) = e (Ideal.Quotient.mk I a)) :
    f = liftHom I J hJ e :=
  Algebra.FormallyUnramified.ext J hJ fun a =>
    (hf a).trans (liftHom_reduction I J hJ e a).symm

variable [Algebra.FormallyEtale R B]

/-- Lifting the inverse reduction gives an actual inverse, by infinitesimal uniqueness. -/
theorem liftHom_comp_symm :
    (liftHom I J hJ e).comp (liftHom J I hI e.symm) = AlgHom.id R B := by
  apply Algebra.FormallyUnramified.ext J hJ
  intro b
  simp only [AlgHom.comp_apply, liftHom_reduction, AlgEquiv.apply_symm_apply,
    AlgHom.id_apply]

/-- The unique lift of a reduced equivalence is an equivalence of the original algebras. -/
def liftEquiv : A ≃ₐ[R] B :=
  AlgEquiv.ofAlgHom (liftHom I J hJ e) (liftHom J I hI e.symm)
    (liftHom_comp_symm I J hI hJ e) (liftHom_comp_symm J I hJ hI e.symm)

/-- The whole equivalence reduces to the specified comparison on every element. -/
theorem liftEquiv_reduction (a : A) :
    Ideal.Quotient.mk J (liftEquiv I J hI hJ e a) = e (Ideal.Quotient.mk I a) :=
  liftHom_reduction I J hJ e a

/-- A reduced equivalence determines its lift independently of all construction choices. -/
theorem liftEquiv_unique (f : A ≃ₐ[R] B)
    (hf : ∀ a, Ideal.Quotient.mk J (f a) = e (Ideal.Quotient.mk I a)) :
    f = liftEquiv I J hI hJ e := by
  apply AlgEquiv.coe_toAlgHom_injective
  exact liftHom_unique I J hJ e f.toAlgHom hf

/-- Lifting the identity reduction gives the identity on the entire etale algebra. -/
theorem liftEquiv_refl :
    liftEquiv I I hI hI ((AlgEquiv.refl : (A ⧸ I) ≃ₐ[R] (A ⧸ I))) = (AlgEquiv.refl : A ≃ₐ[R] A) :=
  (liftEquiv_unique I I hI hI ((AlgEquiv.refl : (A ⧸ I) ≃ₐ[R] (A ⧸ I)))
    ((AlgEquiv.refl : A ≃ₐ[R] A)) (fun _ => rfl)).symm

/-- Lifting respects composition, giving the actual overlap cocycle before reduction. -/
theorem liftEquiv_trans {C : Type*} [CommRing C] [Algebra R C]
    [Algebra.FormallyEtale R C] (K : Ideal C) (hK : IsNilpotent K)
    (f : (B ⧸ J) ≃ₐ[R] (C ⧸ K)) :
    (liftEquiv I J hI hJ e).trans (liftEquiv J K hJ hK f) =
      liftEquiv I K hI hK (e.trans f) := by
  apply liftEquiv_unique
  intro a
  rw [AlgEquiv.trans_apply, liftEquiv_reduction, liftEquiv_reduction]
  rfl

end FLT.Mazur.NilpotentEtale
