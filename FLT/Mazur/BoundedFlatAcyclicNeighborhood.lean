/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundedFlatAcyclicOpen

/-!
# Universal acyclicity on a principal neighborhood of an acyclic fiber

After shrinking around one acyclic residue fiber, positive exactness holds
for every module over the principal localization. Thus the neighborhood
controls nonflat coefficient extensions as well as residue fields.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.BoundedFlatVanishingStalks
open LocalizedTensorCancellation LocalizedHomologyComparison

variable {R : Type} [CommRing R] (C : ℕ → Type)
  [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)] [∀ n, Module.Flat R (C n)]
  (d : ∀ n, C n →ₗ[R] C (n + 1)) (hdd : ∀ n, (d (n + 1)).comp (d n) = 0)
  (b : ℕ) (hb : ∀ n, b ≤ n → Subsingleton (C n))

include hdd hb in
/-- Localized homology vanishing gives exactness for any already-localized coefficients. -/
theorem tensor_exact_of_localized_homology (S : Submonoid R)
    (hH : ∀ n, Subsingleton (LocalizedModule S
      ((d (n + 1)).ker ⧸ (d n).range.comap (d (n + 1)).ker.subtype)))
    (B : Type) [AddCommGroup B] [Module R B] [Module (Localization S) B]
    [IsScalarTower R (Localization S) B] (n : ℕ) :
    Function.Exact ((d n).lTensor B) ((d (n + 1)).lTensor B) := by
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
  exact (tensor_exact_iff S B (d n) (d (n + 1))).mp
    (TensorKernelFlatCokernel.lTensor_exact_of_cokernel_flat (D n) (D (n + 1)) hex B)

variable
  [∀ n, Module.Finite R ((d (n + 1)).ker ⧸ (d n).range.comap (d (n + 1)).ker.subtype)]

include hdd hb in
/-- One acyclic residue fiber has a neighborhood universally acyclic in positive degrees. -/
theorem exists_principal_universally_acyclic (p : PrimeSpectrum R)
    (hp : ∀ n, Function.Exact ((d n).lTensor p.asIdeal.ResidueField)
      ((d (n + 1)).lTensor p.asIdeal.ResidueField)) :
    ∃ r ∉ p.asIdeal, ∀ (B : Type) [AddCommGroup B] [Module R B]
      [Module (Localization.Away r) B] [IsScalarTower R (Localization.Away r) B], ∀ n,
        Function.Exact ((d n).lTensor B) ((d (n + 1)).lTensor B) := by
  obtain ⟨r, hr, _, hH⟩ := exists_principal_acyclic C d hdd b hb p hp
  exact ⟨r, hr, fun B _ _ _ _ n ↦
    tensor_exact_of_localized_homology C d hdd b hb (.powers r) hH B n⟩

end FLT.Mazur.BoundedFlatVanishingStalks
