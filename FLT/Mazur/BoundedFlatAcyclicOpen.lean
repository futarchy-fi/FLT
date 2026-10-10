/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundedFlatVanishingStalks
public import Mathlib.RingTheory.Spectrum.Prime.Module

/-!
# The open acyclic-fiber locus of a bounded flat complex

Finite positive homology has closed support. Boundedness reduces all positive
degrees to a finite intersection, giving the actual residue-acyclic open and
one principal neighborhood on which all positive homology vanishes at once.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.BoundedFlatVanishingStalks
open TopologicalSpace

variable {R : Type} [CommRing R] (C : ℕ → Type)
  [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
  (d : ∀ n, C n →ₗ[R] C (n + 1)) (hdd : ∀ n, (d (n + 1)).comp (d n) = 0)
  [∀ n, Module.Finite R ((d (n + 1)).ker ⧸ (d n).range.comap (d (n + 1)).ker.subtype)]
  (b : ℕ) (hb : ∀ n, b ≤ n → Subsingleton (C n))

/-- The finite intersection of complements of the actual positive homology supports. -/
def acyclicOpen : Opens (PrimeSpectrum R) :=
  ⟨⋂ n : Fin b, (Module.support R
    ((d (n + 1)).ker ⧸ (d n).range.comap (d (n + 1)).ker.subtype))ᶜ,
    isOpen_iInter_of_finite fun _ ↦ Module.isClosed_support.isOpen_compl⟩

include hb in
/-- The bound makes this finite support condition equivalent to the condition in all degrees. -/
lemma mem_acyclicOpen_iff_support (p : PrimeSpectrum R) :
    p ∈ acyclicOpen C d b ↔ ∀ n, p ∉ Module.support R
      ((d (n + 1)).ker ⧸ (d n).range.comap (d (n + 1)).ker.subtype) := by
  simp only [acyclicOpen, Opens.mem_mk, Set.mem_iInter, Set.mem_compl_iff]
  constructor
  · intro h n
    by_cases hn : n < b
    · exact h ⟨n, hn⟩
    · let _ := hb (n + 1) (by omega)
      rw [Module.support_eq_empty]
      exact Set.notMem_empty p
  · intro h n
    exact h n

variable [∀ n, Module.Flat R (C n)]

include hdd hb in
/-- Membership is precisely positive exactness on the original residue-field complex. -/
theorem mem_acyclicOpen_iff (p : PrimeSpectrum R) :
    p ∈ acyclicOpen C d b ↔ ∀ n,
      Function.Exact ((d n).lTensor p.asIdeal.ResidueField)
        ((d (n + 1)).lTensor p.asIdeal.ResidueField) := by
  rw [mem_acyclicOpen_iff_support C d b hb,
    residue_exact_iff_notMem_support C d hdd b hb]

include hdd hb in
/-- Positive acyclicity of residue fibers is open without finite generation of the terms. -/
theorem isOpen_residue_acyclic :
    IsOpen {p : PrimeSpectrum R | ∀ n,
      Function.Exact ((d n).lTensor p.asIdeal.ResidueField)
        ((d (n + 1)).lTensor p.asIdeal.ResidueField)} := by
  convert (acyclicOpen C d b).isOpen using 1
  ext p
  exact (mem_acyclicOpen_iff C d hdd b hb p).symm

include hdd hb in
/-- A single principal neighborhood kills every positive homology module simultaneously. -/
theorem exists_principal_acyclic (p : PrimeSpectrum R)
    (hp : ∀ n, Function.Exact ((d n).lTensor p.asIdeal.ResidueField)
      ((d (n + 1)).lTensor p.asIdeal.ResidueField)) :
    ∃ r ∉ p.asIdeal, PrimeSpectrum.basicOpen r ≤ acyclicOpen C d b ∧
      ∀ n, Subsingleton (LocalizedModule.Away r
        ((d (n + 1)).ker ⧸ (d n).range.comap (d (n + 1)).ker.subtype)) := by
  have hm := (mem_acyclicOpen_iff C d hdd b hb p).mpr hp
  obtain ⟨V, ⟨_, ⟨r, rfl⟩, rfl⟩, hp, hV⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hm (acyclicOpen C d b).isOpen
  refine ⟨r, hp, hV, fun n ↦ ?_⟩
  apply LocalizedModule.subsingleton_iff_support_subset.mpr
  intro q hq
  change ∀ x ∈ ({r} : Set R), x ∈ q.asIdeal
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  by_contra hr
  exact (mem_acyclicOpen_iff_support C d b hb q).mp (hV hr) n hq

end FLT.Mazur.BoundedFlatVanishingStalks
