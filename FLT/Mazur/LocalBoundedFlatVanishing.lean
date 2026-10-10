/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundedFlatFiberVanishing

/-!
# A single closed fiber detects local bounded acyclicity

Over a local ring, finite positive homology and exactness on the closed fiber
suffice. Descending from the bound first makes the outgoing cokernel flat;
Nakayama then kills the next homology. No flatness of homology is assumed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.LocalBoundedFlatVanishing
open FlatCokernelStep FiniteHomologyFiberVanishing

universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] (C : ℕ → Type u)
  [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)] [∀ n, Module.Flat R (C n)]
  (d : ∀ n, C n →ₗ[R] C (n + 1)) (hdd : ∀ n, (d (n + 1)).comp (d n) = 0)
  [∀ n, Module.Finite R ((d (n + 1)).ker ⧸ (d n).range.comap (d (n + 1)).ker.subtype)]
  (b : ℕ) (hb : ∀ n, b ≤ n → Subsingleton (C n))
  (hres : ∀ n, Function.Exact ((d n).lTensor (IsLocalRing.ResidueField R))
    ((d (n + 1)).lTensor (IsLocalRing.ResidueField R)))

include hdd hb hres in
/-- The closed fiber alone makes every differential cokernel flat over the local base. -/
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
    let _ := (IsLocalRing.subsingleton_tensorProduct (R := R)).mp
      (tensor_homology_subsingleton (d n) (d (n + 1)) (hdd n)
        (IsLocalRing.ResidueField R) (hres n))
    exact cokernel_flat_of_homology_flat (d n) (d (n + 1)) (hdd n)

include hdd hb hres in
/-- Actual positive homology vanishes over the local ring if its closed fiber is acyclic. -/
theorem positive_homology_subsingleton (n : ℕ) :
    Subsingleton ((d (n + 1)).ker ⧸ (d n).range.comap (d (n + 1)).ker.subtype) := by
  let _ := cokernel_flat C d hdd b hb hres (n + 1)
  exact (IsLocalRing.subsingleton_tensorProduct (R := R)).mp
    (tensor_homology_subsingleton (d n) (d (n + 1)) (hdd n)
      (IsLocalRing.ResidueField R) (hres n))

include hdd hb hres in
/-- The original local complex is exact in positive degrees. -/
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
/-- Every further coefficient module retains positive exactness. -/
theorem positive_tensor_exact (n : ℕ) (B : Type*) [AddCommGroup B] [Module R B] :
    Function.Exact ((d n).lTensor B) ((d (n + 1)).lTensor B) := by
  let _ := cokernel_flat C d hdd b hb hres (n + 1)
  exact TensorKernelFlatCokernel.lTensor_exact_of_cokernel_flat (d n) (d (n + 1))
    (positive_exact C d hdd b hb hres n) B

end FLT.Mazur.LocalBoundedFlatVanishing
