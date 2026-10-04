/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalHopfPresentation
public import FLT.Mathlib.RingTheory.MvPolynomial.TranslatedVariables

/-! # Square Hopf relations in arbitrary prescribed coordinates -/

@[expose] public noncomputable section

universe u

namespace HopfAlgebra

open MvPolynomial

variable {k A : Type u} [Field k] [CommRing A] [HopfAlgebra k A]
  [IsLocalRing A] [Module.Finite k A]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

include p

/-- Translating by the counit supplies a square relation family without imposing
augmentation-zero conditions on the specified coordinates. -/
theorem exists_relations_of_arbitrary_generators {ι : Type*} [Finite ι]
    (x : ι → A) (hs : Function.Surjective (aeval (R := k) x)) :
    ∃ r : ι → MvPolynomial ι k,
      RingHom.ker (aeval (R := k) x) = Ideal.span (Set.range r) := by
  have : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
  let c : ι → k := fun i ↦ Bialgebra.counitAlgHom k A (x i)
  let y : ι → A := fun i ↦ x i - algebraMap k A (c i)
  let t := translateVariables c
  have hc : aeval (R := k) y = (aeval x).comp t.toAlgHom := by
    ext i
    simp [y, t]
  have hy : ∀ i, Bialgebra.counitAlgHom k A (y i) = 0 := by
    intro i
    simp [y, c]
  have hs' : Function.Surjective (aeval (R := k) y) := by
    rw [hc]
    exact hs.comp t.surjective
  obtain ⟨r, hr⟩ := exists_relations_of_generators p A y hy hs'
  refine ⟨fun i ↦ t (r i), ?_⟩
  have ht : (RingHom.ker (aeval (R := k) y)).map t.toRingHom =
      RingHom.ker (aeval (R := k) x) := by
    rw [hc]
    change ((RingHom.ker (aeval (R := k) x)).comap t.toRingHom).map t.toRingHom = _
    exact Ideal.map_comap_of_surjective t.toRingHom t.surjective _
  rw [← ht, hr, Ideal.map_span, ← Set.range_comp]
  rfl

end HopfAlgebra
