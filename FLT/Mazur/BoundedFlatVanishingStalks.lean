/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalBoundedFlatVanishing
public import FLT.Mazur.LocalizedTensorExactness
public import FLT.Mazur.LocalizedHomologyComparison

/-!
# Fiber acyclicity and stalks of bounded flat homology

For bounded flat complexes with finite positive homology, exactness at one
residue field is equivalent to vanishing of every positive homology stalk.
The proof uses the original complex, not an assumed finite free replacement.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.BoundedFlatVanishingStalks
open LocalizedTensorCancellation LocalizedHomologyComparison

variable {R : Type} [CommRing R] (C : ℕ → Type)
  [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
  (d : ∀ n, C n →ₗ[R] C (n + 1)) (hdd : ∀ n, (d (n + 1)).comp (d n) = 0)
  (b : ℕ) (hb : ∀ n, b ≤ n → Subsingleton (C n))

include hdd in
/-- Localizing differentials retains their square-zero identity. -/
lemma localized_comp (S : Submonoid R) (n : ℕ) :
    (LocalizedModule.map S (d (n + 1))).comp (LocalizedModule.map S (d n)) = 0 := by
  rw [LocalizedKernelComparison.map_comp, hdd, map_zero]

include hb in
/-- The bound survives localization of the original terms. -/
lemma localized_term_subsingleton (S : Submonoid R) (n : ℕ) (hn : b ≤ n) :
    Subsingleton (LocalizedModule S (C n)) := by
  let _ := hb n hn
  infer_instance

variable
  [∀ n, Module.Finite R ((d (n + 1)).ker ⧸ (d n).range.comap (d (n + 1)).ker.subtype)]

include hdd in
/-- Positive localized homology remains finite over the localized ring. -/
theorem localized_homology_finite (S : Submonoid R) (n : ℕ) :
    Module.Finite (Localization S)
      ((LocalizedModule.map S (d (n + 1))).ker ⧸
        (LocalizedModule.map S (d n)).range.comap
          (LocalizedModule.map S (d (n + 1))).ker.subtype) :=
  Module.Finite.equiv (homologyEquiv S (d n) (d (n + 1)) (hdd n))

variable [∀ n, Module.Flat R (C n)]

include hdd hb in
/-- Acyclicity at a residue field kills every positive homology stalk at that prime. -/
theorem homology_stalk_subsingleton (p : PrimeSpectrum R)
    (hres : ∀ n, Function.Exact ((d n).lTensor p.asIdeal.ResidueField)
      ((d (n + 1)).lTensor p.asIdeal.ResidueField)) (n : ℕ) :
    Subsingleton (LocalizedModule p.asIdeal.primeCompl
      ((d (n + 1)).ker ⧸ (d n).range.comap (d (n + 1)).ker.subtype)) := by
  let S := p.asIdeal.primeCompl
  let _ (k : ℕ) := localized_homology_finite C d hdd S k
  have hex (k : ℕ) := (tensor_exact_iff S p.asIdeal.ResidueField (d k) (d (k + 1))).mpr
    (hres k)
  let _ := LocalBoundedFlatVanishing.positive_homology_subsingleton
    (fun k ↦ LocalizedModule S (C k)) (fun k ↦ LocalizedModule.map S (d k))
    (localized_comp C d hdd S) b (localized_term_subsingleton C b hb S) hex n
  exact (homologyEquiv S (d n) (d (n + 1)) (hdd n)).injective.subsingleton

omit [∀ n, Module.Finite R
  ((d (n + 1)).ker ⧸ (d n).range.comap (d (n + 1)).ker.subtype)] in
include hdd hb in
/-- Vanishing of positive homology stalks forces exactness of the residue-field complex. -/
theorem residue_exact_of_homology_stalks (p : PrimeSpectrum R)
    (hH : ∀ n, Subsingleton (LocalizedModule p.asIdeal.primeCompl
      ((d (n + 1)).ker ⧸ (d n).range.comap (d (n + 1)).ker.subtype))) (n : ℕ) :
    Function.Exact ((d n).lTensor p.asIdeal.ResidueField)
      ((d (n + 1)).lTensor p.asIdeal.ResidueField) := by
  let S := p.asIdeal.primeCompl
  let D := fun k ↦ LocalizedModule.map S (d k)
  have hzero (k : ℕ) : Subsingleton ((D (k + 1)).ker ⧸
      (D k).range.comap (D (k + 1)).ker.subtype) := by
    let _ := hH k
    exact (homologyEquiv S (d k) (d (k + 1)) (hdd k)).symm.injective.subsingleton
  have hflat (k : ℕ) : Module.Flat (Localization S) ((D (k + 1)).ker ⧸
      (D k).range.comap (D (k + 1)).ker.subtype) := by
    let _ := hzero k
    infer_instance
  let _ := FlatCokernelStep.bounded_cokernel_flat (fun k ↦ LocalizedModule S (C k))
    D (localized_comp C d hdd S) hflat b (localized_term_subsingleton C b hb S) (n + 1)
  have hex : Function.Exact (D n) (D (n + 1)) := by
    let _ := hzero n
    intro x
    constructor
    · intro hx
      have hz : ((D n).range.comap (D (n + 1)).ker.subtype).mkQ ⟨x, hx⟩ = 0 :=
        Subsingleton.elim _ _
      exact (Submodule.Quotient.mk_eq_zero _).mp hz
    · rintro ⟨y, rfl⟩
      exact LinearMap.congr_fun (localized_comp C d hdd S n) y
  exact (tensor_exact_iff S p.asIdeal.ResidueField (d n) (d (n + 1))).mp
    (TensorKernelFlatCokernel.lTensor_exact_of_cokernel_flat (D n) (D (n + 1))
      hex p.asIdeal.ResidueField)

include hdd hb in
/-- The fiber condition is exactly avoidance of all actual positive homology supports. -/
theorem residue_exact_iff_notMem_support (p : PrimeSpectrum R) :
    (∀ n, Function.Exact ((d n).lTensor p.asIdeal.ResidueField)
      ((d (n + 1)).lTensor p.asIdeal.ResidueField)) ↔
    ∀ n, p ∉ Module.support R
      ((d (n + 1)).ker ⧸ (d n).range.comap (d (n + 1)).ker.subtype) := by
  simp only [Module.notMem_support_iff]
  exact ⟨homology_stalk_subsingleton C d hdd b hb p,
    residue_exact_of_homology_stalks C d hdd b hb p⟩

end FLT.Mazur.BoundedFlatVanishingStalks
