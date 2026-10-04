/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Regular.FaithfullyFlatDescent
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Reflect a presentation through a faithfully flat coordinate square -/

@[expose] public noncomputable section

namespace AlgHom

variable {k R S A B : Type*} [CommRing k] [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] [Algebra k R] [Algebra k S] [Algebra R S]
  [Module.FaithfullyFlat R S] [Algebra k A] [Algebra k B]

/-- Equality of the geometric relation ideal reflects to the original presentation kernel.
The square keeps the specified coordinate maps, and the target comparison is injective. -/
theorem ker_eq_of_faithfullyFlat_square (f : R →ₐ[k] A) (g : S →ₐ[k] B)
    (j : A →ₐ[k] B) (hj : Function.Injective j)
    (hsq : ∀ r, g (algebraMap R S r) = j (f r)) (I : Ideal R)
    (hI : RingHom.ker g = I.map (algebraMap R S)) : RingHom.ker f = I := by
  have hc : (RingHom.ker g).comap (algebraMap R S) = RingHom.ker f := by
    ext r
    change g (algebraMap R S r) = 0 ↔ f r = 0
    rw [hsq, ← j.map_zero]
    exact hj.eq_iff
  rw [hI, Ideal.comap_map_eq_self_of_faithfullyFlat] at hc
  exact hc.symm

/-- A quotient equivalence descends with its original coordinate formula once the
source coordinate map is surjective and the faithfully flat square is specified. -/
def quotientEquivOfFaithfullyFlatSquare (f : R →ₐ[k] A) (hf : Function.Surjective f)
    (g : S →ₐ[k] B) (j : A →ₐ[k] B) (hj : Function.Injective j)
    (hsq : ∀ r, g (algebraMap R S r) = j (f r)) (I : Ideal R)
    (hI : RingHom.ker g = I.map (algebraMap R S)) : (R ⧸ I) ≃ₐ[k] A :=
  (Ideal.quotientEquivAlgOfEq k (f.ker_eq_of_faithfullyFlat_square g j hj hsq I hI).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hf)

@[simp] theorem quotientEquivOfFaithfullyFlatSquare_mk
    (f : R →ₐ[k] A) (hf : Function.Surjective f)
    (g : S →ₐ[k] B) (j : A →ₐ[k] B) (hj : Function.Injective j)
    (hsq : ∀ r, g (algebraMap R S r) = j (f r)) (I : Ideal R)
    (hI : RingHom.ker g = I.map (algebraMap R S)) (r : R) :
    f.quotientEquivOfFaithfullyFlatSquare hf g j hj hsq I hI (Ideal.Quotient.mk I r) = f r :=
  rfl

/-- Regularity and the quotient isomorphism reflect together, preserving coordinates. -/
theorem exists_regular_presentation_of_faithfullyFlat_square
    (f : R →ₐ[k] A) (hf : Function.Surjective f)
    (g : S →ₐ[k] B) (j : A →ₐ[k] B) (hj : Function.Injective j)
    (hsq : ∀ r, g (algebraMap R S r) = j (f r)) (rs : List R)
    (hker : RingHom.ker g = Ideal.ofList (rs.map (algebraMap R S)))
    (hreg : RingTheory.Sequence.IsRegular S (rs.map (algebraMap R S))) :
    RingTheory.Sequence.IsRegular R rs ∧
      ∃ e : (R ⧸ Ideal.ofList rs) ≃ₐ[k] A,
        ∀ r, e (Ideal.Quotient.mk _ r) = f r := by
  rw [← Ideal.map_ofList] at hker
  exact ⟨RingTheory.Sequence.isRegular_iff_of_faithfullyFlat.mp hreg,
    f.quotientEquivOfFaithfullyFlatSquare hf g j hj hsq _ hker, fun _ ↦ rfl⟩

end AlgHom
