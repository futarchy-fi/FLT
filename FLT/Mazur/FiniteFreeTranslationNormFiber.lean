/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeTranslationNorm
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Norm principal opens retain exactly the whole finite translation fiber

The support condition is tested on every prime of the original algebra over
the chosen base point. It is not a condition on a distinguished branch, and
it includes every residue-field branch of the tensor-product fiber.
-/

@[expose] public noncomputable section
open Module TensorProduct
namespace FLT.Mazur.FiniteFreeTranslationNorm
set_option backward.isDefEq.respectTransparency false
universe u v w
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A coefficient is a unit precisely when no point of its spectrum is a zero. -/
theorem isUnit_iff_forall_spectrum (s : S) :
    IsUnit s ↔ ∀ q : PrimeSpectrum S, s ∉ q.asIdeal := by
  constructor
  · intro h q
    exact q.asIdeal.notMem_of_isUnit h
  · intro h
    by_contra hn
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal (Ideal.span {s})
      (mt Ideal.span_singleton_eq_top.mp hn)
    exact h ⟨m, hm.isPrime⟩ (hsm (Ideal.subset_span (Set.mem_singleton s)))

/-- Units in the full residue algebra avoid exactly all original fiber primes. -/
theorem fiber_isUnit_iff (p : PrimeSpectrum R) (s : S) :
    IsUnit (1 ⊗ₜ[R] s : p.asIdeal.Fiber S) ↔
      ∀ q : PrimeSpectrum S, PrimeSpectrum.comap (algebraMap R S) q = p → s ∉ q.asIdeal := by
  rw [isUnit_iff_forall_spectrum]
  let e := PrimeSpectrum.preimageEquivFiber R S p
  constructor
  · intro h q hq
    have he := congrArg Subtype.val (e.symm_apply_apply ⟨q, hq⟩)
    change PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom
      (e ⟨q, hq⟩) = q at he
    have hh := h (e ⟨q, hq⟩)
    change s ∉ (PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom
      (e ⟨q, hq⟩)).asIdeal at hh
    rwa [he] at hh
  · intro h q
    exact h (e.symm q).val (e.symm q).property

variable {ι : Type w} [Finite ι] (b : Basis ι R S)
include b

/-- The norm is nonzero exactly where the whole original fiber avoids the zero set. -/
theorem mem_basicOpen_norm_iff (p : PrimeSpectrum R) (s : S) :
    p ∈ PrimeSpectrum.basicOpen (Algebra.norm R s) ↔
      ∀ q : PrimeSpectrum S, PrimeSpectrum.comap (algebraMap R S) q = p →
        q ∈ PrimeSpectrum.basicOpen s := by
  change Algebra.norm R s ∉ p.asIdeal ↔ _
  exact (not_congr Ideal.algebraMap_residueField_eq_zero).symm.trans
    ((norm_ne_zero_iff b (K := p.asIdeal.ResidueField) s).trans (fiber_isUnit_iff p s))

/-- The norm's principal open is exactly the complement of the image of the zero set. -/
theorem basicOpen_norm_eq (s : S) :
    (PrimeSpectrum.basicOpen (Algebra.norm R s) : Set (PrimeSpectrum R)) =
      (PrimeSpectrum.comap (algebraMap R S) ''
        (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum S))ᶜ)ᶜ := by
  ext p
  change p ∈ PrimeSpectrum.basicOpen (Algebra.norm R s) ↔ _
  rw [mem_basicOpen_norm_iff b]
  simp only [Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
  constructor
  · intro h q hq hp
    exact hq (h q hp)
  · intro h q hp
    by_contra hq
    exact h q hq hp

end FLT.Mazur.FiniteFreeTranslationNorm
