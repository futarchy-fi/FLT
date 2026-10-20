/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# A Jacobson reduction detects full open neighborhoods

An open of an affine spectrum containing a surjective ring reduction with
Jacobson kernel is the whole spectrum. This detects factorization through
an arbitrary open of a target scheme, not only principal opens.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.JacobsonReductionOpenDetection

variable {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
  (hf : Function.Surjective f) (hker : RingHom.ker f ≤ (⊥ : Ideal A).jacobson)

include hf hker

/-- The full reduction meets every closed point and hence detects the whole open. -/
theorem open_eq_top (U : (Spec (.of A)).Opens)
    (hU : Set.range (Spec.map (CommRingCat.ofHom f)) ⊆ U) : U = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨M, hM, hxM⟩ := x.asIdeal.exists_le_maximal x.isPrime.ne_top
  let y : PrimeSpectrum A := ⟨M, hM.isPrime⟩
  have hy : y ∈ Set.range (PrimeSpectrum.comap f) := by
    rw [range_comap_of_surjective B f hf]
    exact hker.trans (sInf_le ⟨bot_le, hM⟩)
  exact ((PrimeSpectrum.le_iff_specializes x y).mp hxM).mem_open U.isOpen (hU hy)

/-- Landing in a target open is detected after the full Jacobson reduction. -/
theorem range_subset {X : Scheme} (q : Spec (.of A) ⟶ X) (U : X.Opens)
    (h : Set.range (Spec.map (CommRingCat.ofHom f) ≫ q) ⊆ U) : Set.range q ⊆ U := by
  have he : q ⁻¹ᵁ U = ⊤ := open_eq_top f hf hker (q ⁻¹ᵁ U) (by
    rintro _ ⟨x, rfl⟩
    exact h ⟨x, rfl⟩)
  rintro _ ⟨x, rfl⟩
  change x ∈ q ⁻¹ᵁ U
  rw [he]
  trivial

end FLT.Mazur.JacobsonReductionOpenDetection
