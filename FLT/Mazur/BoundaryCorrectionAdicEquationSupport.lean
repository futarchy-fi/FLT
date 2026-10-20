/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionAdicEquationIdeal
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Whole scalar-fiber support for the coupled equation ideal

Support must hold on every original boundary and mixed coordinate. These
conditions assemble to the whole fiber in the full equation ring. Noetherian
coordinate rings give finite generation there, not over the invariant scalars.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
namespace FiniteProductAdicIdeals
variable {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C]

/-- Scalar extension to a pair is the pair of the original scalar extensions. -/
theorem scalar_map_prod (J : Ideal R) :
    J.map (algebraMap R (B × C)) =
      (J.map (algebraMap R B)).prod (J.map (algebraMap R C)) := by
  apply (Ideal.idealProdEquiv (R := B) (S := C)).injective
  apply Prod.ext
  · change Ideal.map (RingHom.fst B C) _ = Ideal.map (RingHom.fst B C) _
    rw [Ideal.map_map, Ideal.map_fst_prod]
    rfl
  · change Ideal.map (RingHom.snd B C) _ = Ideal.map (RingHom.snd B C) _
    rw [Ideal.map_map, Ideal.map_snd_prod]
    rfl

/-- One exponent suffices for both coordinates of a radical pair. -/
theorem prod_radical (K : Ideal B) (L : Ideal C) :
    (K.prod L).radical = K.radical.prod L.radical := by
  ext x
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨⟨n, hn.1⟩, ⟨n, hn.2⟩⟩
  · rintro ⟨⟨n, hn⟩, ⟨m, hm⟩⟩
    exact ⟨max n m, K.pow_mem_of_pow_mem hn (le_max_left _ _),
      L.pow_mem_of_pow_mem hm (le_max_right _ _)⟩

/-- Every scalar-fiber point of the pair is controlled by the two coordinate tests. -/
theorem prod_scalar_support (J : Ideal R) (K : Ideal B) (L : Ideal C)
    (hK : PrimeSpectrum.zeroLocus (J.map (algebraMap R B) : Set B) ⊆
      PrimeSpectrum.zeroLocus (K : Set B))
    (hL : PrimeSpectrum.zeroLocus (J.map (algebraMap R C) : Set C) ⊆
      PrimeSpectrum.zeroLocus (L : Set C)) :
    PrimeSpectrum.zeroLocus (J.map (algebraMap R (B × C)) : Set (B × C)) ⊆
      PrimeSpectrum.zeroLocus (K.prod L : Set (B × C)) := by
  apply (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mpr
  rw [scalar_map_prod, prod_radical]
  exact Ideal.prod_mono ((PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp hK)
    ((PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp hL)

end FiniteProductAdicIdeals
namespace BoundaryCorrectionIdeal
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
  {B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)]
  (J : Ideal R) (K : ∀ i, Ideal (B i)) (L : ∀ i j, Ideal (C i j))

/-- The constructed ideal contains the whole original scalar fiber in its vanishing locus. -/
theorem fullEquationIdeal_scalar_support
    (hb : ∀ i, PrimeSpectrum.zeroLocus (J.map (algebraMap R (B i)) : Set (B i)) ⊆
      PrimeSpectrum.zeroLocus (K i : Set (B i)))
    (hm : ∀ i j, PrimeSpectrum.zeroLocus
      (J.map (algebraMap R (C i j)) : Set (C i j)) ⊆
        PrimeSpectrum.zeroLocus (L i j : Set (C i j))) :
    PrimeSpectrum.zeroLocus
      (J.map (algebraMap R ((∀ i, B i) × ∀ i j, C i j)) :
        Set ((∀ i, B i) × ∀ i j, C i j)) ⊆
        PrimeSpectrum.zeroLocus (fullEquationIdeal K L : Set ((∀ i, B i) × ∀ i j, C i j)) :=
  FiniteProductAdicIdeals.prod_scalar_support J _ _
    (FiniteProductAdicIdeals.pi_scalar_support J K hb)
    (FiniteProductAdicIdeals.pi_scalar_support J _ fun i ↦
      FiniteProductAdicIdeals.pi_scalar_support J (L i) (hm i))

omit [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)] in
/-- Noetherian coordinates make the full equation ideal finitely generated in its own ring. -/
theorem fullEquationIdeal_fg [∀ i, IsNoetherianRing (B i)]
    [∀ i j, IsNoetherianRing (C i j)] : (fullEquationIdeal K L).FG :=
  (fullEquationIdeal K L).fg_of_isNoetherianRing

/-- One positive cofinal order controls every boundary and mixed coordinate simultaneously. -/
theorem fullEquationIdeal_scalar_bound (hfg : (fullEquationIdeal K L).FG)
    (hb : ∀ i, PrimeSpectrum.zeroLocus (J.map (algebraMap R (B i)) : Set (B i)) ⊆
      PrimeSpectrum.zeroLocus (K i : Set (B i)))
    (hm : ∀ i j, PrimeSpectrum.zeroLocus
      (J.map (algebraMap R (C i j)) : Set (C i j)) ⊆
        PrimeSpectrum.zeroLocus (L i j : Set (C i j))) :
    ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, fullEquationIdeal K L ^ (c * n) ≤
      (J ^ n).map (algebraMap R ((∀ i, B i) × ∀ i j, C i j)) :=
  AdicIdealPowerComparison.exists_power_bound_of_support J _ hfg
    (fullEquationIdeal_scalar_support J K L hb hm)

/-- Coupled coordinate errors at all orders give every original scalar approximation. -/
theorem fullEquationIdeal_scalar_approximations
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (φ : ∀ i, A i →ₐ[R] B i)
    (p : ∀ i j, A i →ₐ[R] C i j) (q : ∀ i j, A j →ₐ[R] C i j)
    (hfg : (fullEquationIdeal K L).FG)
    (hb : ∀ i, PrimeSpectrum.zeroLocus (J.map (algebraMap R (B i)) : Set (B i)) ⊆
      PrimeSpectrum.zeroLocus (K i : Set (B i)))
    (hm : ∀ i j, PrimeSpectrum.zeroLocus
      (J.map (algebraMap R (C i j)) : Set (C i j)) ⊆
        PrimeSpectrum.zeroLocus (L i j : Set (C i j)))
    (t : ∀ i, B i)
    (h : ∀ n : ℕ, ∃ w : ∀ i, A i,
      (∀ i, t i - φ i (w i) ∈ K i ^ (n + 1)) ∧
        ∀ i j, p i j (w i) - q i j (w j) ∈ L i j ^ (n + 1)) :
    ∀ n : ℕ, ∃ w : ∀ i, A i,
      (t, 0) - originalCorrectionOperator φ p q 0 w ∈
        J ^ (n + 1) • (⊤ : Submodule R ((∀ i, B i) × ∀ i j, C i j)) := by
  apply AdicIdealPowerComparison.scalar_approximations J (fullEquationIdeal K L)
    (originalCorrectionOperator φ p q 0) (t, 0) hfg
    ((PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp
      (fullEquationIdeal_scalar_support J K L hb hm))
  intro n
  obtain ⟨w, hwb, hwm⟩ := h n
  exact ⟨w, original_error_mem_fullEquationIdeal φ p q K L (n + 1) t w hwb hwm⟩

end BoundaryCorrectionIdeal
end FLT.Mazur
