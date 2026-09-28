/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FrobeniusRelativePresentation
public import FLT.Mathlib.RingTheory.MvPolynomial.FrobeniusGenerators
public import FLT.Mathlib.RingTheory.MvPolynomial.FrobeniusRelationDescent

/-! # Frobenius descent in prescribed minimal coordinates -/

@[expose] public noncomputable section

universe u

namespace HopfAlgebra

open MvPolynomial

variable {k A : Type u} [Field k] [CommRing A] [HopfAlgebra k A]
  [IsLocalRing A] [Module.Finite k A]
  (p : ℕ) [Fact p.Prime] [CharP k p] [CharP A p] [PerfectRing k p]

/-- Coordinate derivations identify the absolute kernel with the expansion
of the kernel of the coordinate powers in the Frobenius image. -/
theorem ker_aeval_eq_map_expand_of_coordinate {ι : Type*} [DecidableEq ι]
    (x : ι → A) (hx : ∀ i, Bialgebra.counitAlgHom k A (x i) = 0)
    (hsurj : Function.Surjective (aeval (R := k) x))
    (D : ι → Derivation k A A) (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (z : ι → Algebra.frobeniusImage k A p 1) (hz : ∀ i, (z i : A) = x i ^ p) :
    RingHom.ker (aeval (R := k) x) =
      (RingHom.ker (aeval (R := k) z)).map (expand p).toRingHom := by
  let ε := Bialgebra.counitAlgHom k A
  let I := RingHom.ker ε
  let F := Algebra.frobeniusImage k A p 1
  let εF : F →ₐ[k] k := ε.comp F.val
  let : IsLocalRing F := Algebra.isLocalRing_frobeniusImage k A p 1
  let : Module.Free F A := free_frobeniusImage p
  let J := I.frobeniusPower p
  let q : A →ₐ[k] A ⧸ J := Ideal.Quotient.mkₐ k J
  have hq (c : F) : q (algebraMap F A c) = algebraMap k (A ⧸ J) (εF c) := by
    rw [← q.commutes]
    apply Ideal.Quotient.eq.mpr
    change (c : A) - algebraMap k A (εF c) ∈ I.frobeniusPower p
    rw [ε.frobeniusPower_ker_eq_map_ker_frobeniusImage p]
    have hc : c - algebraMap k F (εF c) ∈ RingHom.ker εF := by
      simp [RingHom.mem_ker]
    exact Ideal.mem_map_of_mem F.val hc
  have hsurjF : Function.Surjective (aeval (R := F) x) := by
    intro a
    obtain ⟨f, hf⟩ := hsurj a
    refine ⟨map (algebraMap k F) f, ?_⟩
    simpa only [aeval_def, eval₂_map, IsScalarTower.algebraMap_eq k F A] using hf
  have hdiag : (Ideal.Quotient.mkₐ k J).comp (aeval (R := k) x) =
      aeval (R := k) (fun i ↦ q (x i)) := by
    ext i
    simp only [AlgHom.comp_apply, aeval_X]
    rfl
  have hker := ε.ker_frobeniusQuotient_aeval_of_coordinate p x hx D hD
  rw [hdiag] at hker
  have hzε (i : ι) : εF (z i) = 0 := by
    change ε (z i : A) = 0
    rw [hz, map_pow, hx i, zero_pow (Fact.out : p.Prime).ne_zero]
  have hpow (i : ι) : x i ^ p = algebraMap F A (z i) := (hz i).symm
  have hrel := ker_aeval_eq_span_of_nilpotent_reduction εF
    εF.isNilpotent_ker_of_finite_local q hq x hsurjF p z hzε hpow hker
  exact ker_aeval_eq_map_expand_of_relative_presentation x p z
    (aeval_frobeniusCoordinates_surjective p x hsurj z hz) hpow hrel

end HopfAlgebra
