/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Bounding finite-algebra point counts by dimension

Chinese remaindering surjects onto all residue fields simultaneously. Each
residue field has positive dimension, so the number of spectrum points is
at most the dimension of the algebra. Neither reducedness nor splitting
of residue fields is needed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteAlgebraSpectrumCard

universe u v
variable (K : Type u) [Field K] (B : Type v) [CommRing B] [Algebra K B]
  [Module.Finite K B]

/-- Every point contributes at least one dimension through its residue field. -/
theorem card_primeSpectrum_le_finrank : Nat.card (PrimeSpectrum B) ≤ Module.finrank K B := by
  classical
  let _ : IsArtinianRing B := isArtinian_of_tower K inferInstance
  let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  let g : B →ₗ[K] (∀ m : MaximalSpectrum B, B ⧸ m.asIdeal) :=
    (LinearMap.pi fun m : MaximalSpectrum B ↦ m.asIdeal.mkQ).restrictScalars K
  have hg : Function.Surjective g :=
    Ideal.pi_mkQ_surjective (fun _ _ h ↦ MaximalSpectrum.isCoprime_of_ne h)
  have hdim := LinearMap.finrank_le_finrank_of_surjective hg
  have hsum : Fintype.card (MaximalSpectrum B) ≤
      ∑ m : MaximalSpectrum B, Module.finrank K (B ⧸ m.asIdeal) := by
    calc
      Fintype.card (MaximalSpectrum B) = ∑ _m : MaximalSpectrum B, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun m _ ↦ Nat.succ_le_of_lt (Module.finrank_pos (R := K)))
  rw [Module.finrank_pi_fintype] at hdim
  rw [Nat.card_congr (IsArtinianRing.primeSpectrumEquivMaximalSpectrum (R := B)),
    Nat.card_eq_fintype_card]
  exact hsum.trans hdim

end FLT.Mazur.FiniteAlgebraSpectrumCard
