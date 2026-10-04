/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ComponentLocalizedKernel
public import FLT.GroupScheme.FiniteHopfComponentCoordinatePresentation

/-! # The original geometric Hopf presentation at each geometric point -/

@[expose] public noncomputable section

universe u

namespace HopfAlgebra

open FiniteAlgebra MvPolynomial

variable {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A] [HopfAlgebra k A]
  [IsArtinianRing A] [Module.Finite k A]
  (p : ℕ) [Fact p.Prime] [CharP k p]

include p

/-- Localizing the original geometric presentation at a point gives a square kernel
and the actual component quotient, in the prescribed coordinates. -/
theorem exists_geometric_point_kernel (ε : A →ₐ[k] k) {n : ℕ}
    (f : MvPolynomial (Fin n) k →ₐ[k] A) (hf : Function.Surjective f) :
    let a := fun i ↦ ε (f (X i))
    let L := Localization.AtPrime (rationalPointIdeal a)
    ∃ (v : Fin n → L) (_e : (L ⧸ (RingHom.ker f).map (algebraMap _ L)) ≃ₐ[k]
        PointComponent ε),
      (RingHom.ker f).map (algebraMap _ L) = Ideal.span (Set.range v) := by
  let q := (pointProjection ε).comp f
  let x := fun i ↦ q (X i)
  have hq : aeval (R := k) x = q := by ext i; simp [x]
  have hqs : Function.Surjective (aeval (R := k) x) := by
    rw [hq]
    exact Ideal.Quotient.mk_surjective.comp hf
  obtain ⟨r, hr⟩ := exists_component_relations_of_generators p (pointComponentIndex ε) x hqs
  have hpoint : (ε.comp f) = aeval (fun i ↦ ε (f (X i))) := by ext i; simp
  have hP : (IsLocalRing.maximalIdeal (PointComponent ε)).comap q =
      rationalPointIdeal (fun i ↦ ε (f (X i))) := by
    rw [← hq, comap_maximalIdeal_aeval_at_point (componentPoint ε) x]
    rfl
  have hI : (RingHom.ker f).map (algebraMap _
      (Localization.AtPrime (rationalPointIdeal (fun i ↦ ε (f (X i)))))) =
      (RingHom.ker q).map (algebraMap _
        (Localization.AtPrime (rationalPointIdeal (fun i ↦ ε (f (X i)))))) := by
    have h := map_ker_eq_component_localized ε f hf
    rw [hpoint] at h
    exact h
  let L := Localization.AtPrime (rationalPointIdeal (fun i ↦ ε (f (X i))))
  have key (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
      (hP : P = (IsLocalRing.maximalIdeal (PointComponent ε)).comap
        (q : MvPolynomial (Fin n) k →+* PointComponent ε)) :
      Nonempty ((Localization.AtPrime P ⧸
        (RingHom.ker q).map (algebraMap _ (Localization.AtPrime P))) ≃ₐ[k] PointComponent ε) := by
    subst P
    change Nonempty ((q.localizedSource ⧸
      (RingHom.ker q).map (algebraMap _ q.localizedSource)) ≃ₐ[k] PointComponent ε)
    rw [← q.ker_localizeAtMaximal]
    exact ⟨Ideal.quotientKerAlgEquivOfSurjective
      (q.localizeAtMaximal_surjective (Ideal.Quotient.mk_surjective.comp hf))⟩
  have hlocal := key _ hP.symm
  refine ⟨fun i ↦ algebraMap _ L (r i), ?_, ?_⟩
  · exact (Ideal.quotientEquivAlgOfEq k hI).trans hlocal.some
  · rw [hI, ← hq, hr, Ideal.map_span, ← Set.range_comp]
    rfl

end HopfAlgebra
