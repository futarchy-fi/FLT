/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeEffectiveEpiSections

/-!
# Idempotent regular functions detect clopen supports

An affine clopen has an actual idempotent equation. Idempotent equations with
identical support agree even on nonaffine schemes and in the presence of
nilpotents. This permits invariance to be proved from clopen geometry.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeIdempotentSupport
open SchemeEffectiveEpiSections
universe u

/-- An affine clopen is cut out by an actual idempotent global section. -/
theorem exists_idempotent {X : Scheme.{u}} [IsAffine X]
    (U : X.Opens) (hU : IsClosed (U : Set X)) :
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧ X.basicOpen e = U := by
  have hc : IsClopen (X.isoSpec.hom '' (U : Set X)) :=
    ⟨X.isoSpec.hom.homeomorph.isClosedMap _ hU,
      X.isoSpec.hom.isOpenMap _ U.isOpen⟩
  obtain ⟨e, he, h⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hc
  refine ⟨e, he, ?_⟩
  have hh : X.isoSpec.hom ''ᵁ U = PrimeSpectrum.basicOpen e := SetLike.ext' h
  have hh' := congrArg (X.isoSpec.hom ⁻¹ᵁ ·) hh
  rw [X.isoSpec.hom.preimage_image_eq, Scheme.isoSpec_hom,
    Scheme.toSpecΓ_preimage_basicOpen] at hh'
  exact hh'.symm

/-- On an affine scheme, idempotent sections with the same support are equal. -/
theorem eq_of_basicOpen_eq_affine {X : Scheme.{u}} [IsAffine X]
    {e t : Γ(X, ⊤)} (he : IsIdempotentElem e) (ht : IsIdempotentElem t)
    (h : X.basicOpen e = X.basicOpen t) : e = t := by
  apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he ht
  apply SetLike.coe_injective
  apply Set.preimage_injective.mpr X.isoSpec.hom.homeomorph.surjective
  change (X.isoSpec.hom ⁻¹ᵁ PrimeSpectrum.basicOpen e : Set X) =
    (X.isoSpec.hom ⁻¹ᵁ PrimeSpectrum.basicOpen t : Set X)
  simpa only [Scheme.isoSpec_hom, Scheme.toSpecΓ_preimage_basicOpen] using
    congrArg SetLike.coe h

/-- Nilpotents do not obstruct idempotent uniqueness on arbitrary schemes. -/
theorem eq_of_basicOpen_eq {X : Scheme.{u}} {e t : Γ(X, ⊤)}
    (he : IsIdempotentElem e) (ht : IsIdempotentElem t)
    (h : X.basicOpen e = X.basicOpen t) : e = t := by
  apply (functionEquiv X).symm.injective
  apply X.affineCover.hom_ext
  intro i
  apply (functionEquiv _).injective
  simp only [functionEquiv_comp, Equiv.apply_symm_apply]
  apply eq_of_basicOpen_eq_affine (he.map (X.affineCover.f i).appTop.hom)
    (ht.map (X.affineCover.f i).appTop.hom)
  rw [← Scheme.preimage_basicOpen_top, ← Scheme.preimage_basicOpen_top, h]

/-- A clopen invariant under two endpoints has an invariant idempotent equation. -/
theorem exists_invariant_idempotent {X D : Scheme.{u}} [IsAffine X]
    (p q : D ⟶ X) (U : X.Opens) (hU : IsClosed (U : Set X))
    (hi : p ⁻¹ᵁ U = q ⁻¹ᵁ U) :
    ∃ e : compatibleFunctions p q, IsIdempotentElem e.val ∧ X.basicOpen e.val = U := by
  obtain ⟨e, he, h⟩ := exists_idempotent U hU
  refine ⟨⟨e, ?_⟩, he, h⟩
  apply eq_of_basicOpen_eq (he.map p.appTop.hom) (he.map q.appTop.hom)
  rw [← Scheme.preimage_basicOpen_top, ← Scheme.preimage_basicOpen_top, h, hi]

end FLT.Mazur.SchemeIdempotentSupport
