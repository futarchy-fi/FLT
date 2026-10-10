/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteHomologyFiberVanishing
public import FLT.Mazur.AcyclicTensorExactness

/-!
# Residue fibers detect acyclicity of bounded flat complexes

For a bounded flat complex with finite positive homology, exactness in every
positive degree on every residue fiber forces actual positive acyclicity.
Descending induction also proves flatness of all differential cokernels, so
positive exactness survives arbitrary further coefficient extension.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.BoundedFlatFiberVanishing
open FlatCokernelStep FiniteHomologyFiberVanishing

universe u
variable {R : Type u} [CommRing R] (C : ℕ → Type u)
  [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)] [∀ n, Module.Flat R (C n)]
  (d : ∀ n, C n →ₗ[R] C (n + 1)) (hdd : ∀ n, (d (n + 1)).comp (d n) = 0)
  [∀ n, Module.Finite R ((d (n + 1)).ker ⧸ (d n).range.comap (d (n + 1)).ker.subtype)]
  (b : ℕ) (hb : ∀ n, b ≤ n → Subsingleton (C n))
  (hres : ∀ (p : PrimeSpectrum R) n,
    Function.Exact ((d n).lTensor p.asIdeal.ResidueField)
      ((d (n + 1)).lTensor p.asIdeal.ResidueField))

include hdd hb hres in
/-- Residue-field acyclicity makes every differential cokernel flat. -/
theorem cokernel_flat (n : ℕ) : Module.Flat R (C (n + 1) ⧸ (d n).range) := by
  suffices ∀ k n, b ≤ n + k → Module.Flat R (C (n + 1) ⧸ (d n).range) from
    this b n (by omega)
  intro k
  induction k with
  | zero =>
    intro n hn
    let _ := hb (n + 1) (by omega)
    infer_instance
  | succ k ih =>
    intro n hn
    let _ := ih (n + 1) (by omega)
    let _ := homology_subsingleton_of_residue_fields (d n) (d (n + 1)) (hdd n)
      (fun p ↦ hres p n)
    exact cokernel_flat_of_homology_flat (d n) (d (n + 1)) (hdd n)

include hdd hb hres in
/-- Every actual positive homology group vanishes, including over nonreduced bases. -/
theorem positive_homology_subsingleton (n : ℕ) :
    Subsingleton ((d (n + 1)).ker ⧸ (d n).range.comap (d (n + 1)).ker.subtype) := by
  let _ := cokernel_flat C d hdd b hb hres (n + 1)
  exact homology_subsingleton_of_residue_fields (d n) (d (n + 1)) (hdd n)
    (fun p ↦ hres p n)

include hdd hb hres in
/-- The original complex is exact in every positive degree. -/
theorem positive_exact (n : ℕ) : Function.Exact (d n) (d (n + 1)) := by
  let _ := positive_homology_subsingleton C d hdd b hb hres n
  intro x
  constructor
  · intro hx
    have hz : ((d n).range.comap (d (n + 1)).ker.subtype).mkQ ⟨x, hx⟩ = 0 :=
      Subsingleton.elim _ _
    exact (Submodule.Quotient.mk_eq_zero _).mp hz
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (hdd n) y

include hdd hb hres in
/-- Fiberwise exactness implies positive exactness with arbitrary coefficients. -/
theorem positive_tensor_exact (n : ℕ) (B : Type*) [AddCommGroup B] [Module R B] :
    Function.Exact ((d n).lTensor B) ((d (n + 1)).lTensor B) := by
  let _ := cokernel_flat C d hdd b hb hres (n + 1)
  exact TensorKernelFlatCokernel.lTensor_exact_of_cokernel_flat (d n) (d (n + 1))
    (positive_exact C d hdd b hb hres n) B

end FLT.Mazur.BoundedFlatFiberVanishing
