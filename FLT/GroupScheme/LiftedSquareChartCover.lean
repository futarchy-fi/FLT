/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LiftedChartCover
public import FLT.GroupScheme.LiftedSquarePresentationFlat

/-! # A faithfully flat cover built from actual lifted square chart equations -/

@[expose] public noncomputable section

namespace Algebra.Presentation

variable {B C ι : Type*} [CommRing B] [CommRing C] [Algebra B C] [Finite ι]
  (E : ι → Type*) [∀ i, CommRing (E i)] [∀ i, Algebra C (E i)]
  [∀ i, Algebra B (E i)] [∀ i, IsScalarTower B C (E i)]
  [∀ i, QuasiFinite C (E i)] (n : ι → ℕ)
  (P : ∀ i, Presentation C (E i) (Fin (n i)) (Fin (n i)))
  (g : ∀ i, Fin (n i) → MvPolynomial (Fin (n i)) B)
  (hg : ∀ i j, MvPolynomial.map (algebraMap B C) (g i j) = (P i).relation j)

include P hg in
/-- Flatness of the lifted charts is proved from their reduced square presentations.
Their finite product is faithfully flat because the original reduced charts cover. -/
theorem faithfullyFlat_liftedSquareChartCover
    (hq : Function.Surjective (algebraMap B C)) {m : ℕ}
    (hn : RingHom.ker (algebraMap B C) ^ m = ⊥)
    (hcover : ∀ Q : PrimeSpectrum C, ∃ i, ∃ U : PrimeSpectrum (E i),
      PrimeSpectrum.comap (algebraMap C (E i)) U = Q) :
    Module.FaithfullyFlat B
      (∀ i, MvPolynomial (Fin (n i)) B ⧸ Ideal.span (Set.range (g i))) := by
  let D := fun i ↦ MvPolynomial (Fin (n i)) B ⧸ Ideal.span (Set.range (g i))
  have : ∀ i, Module.Flat B (D i) := fun i ↦
    (P i).flat_liftedSquarePresentation (g i) (hg i) hq hn
  apply Module.FaithfullyFlat.pi_of_nilpotent_cover_charts D E (algebraMap B C) hq
    (fun b hb ↦ ⟨m, by
      have hm := Ideal.pow_mem_pow hb m
      rwa [hn, Ideal.mem_bot] at hm⟩)
    (fun i ↦ ((P i).liftedRelationAlgHom (g i) (hg i)).toRingHom) ?_ hcover
  intro i
  ext b
  exact (((P i).liftedRelationAlgHom (g i) (hg i)).commutes b).trans
    (IsScalarTower.algebraMap_apply B C (E i) b)

end Algebra.Presentation
