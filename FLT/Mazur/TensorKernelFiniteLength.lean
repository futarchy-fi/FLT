/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorKernelExtension
public import Mathlib.RingTheory.FiniteLength

/-!
# Tensor-kernel dévissage for finite-length coefficients

An augmented complex with flat final term is exact with every finite-length
coefficient module once it is exact with simple coefficients. In particular,
checking residue-field coefficients suffices over an Artinian base ring.
-/

@[expose] public noncomputable section
open TensorProduct
universe v
namespace FLT.Mazur.TensorKernelFiniteLength
open TensorKernelExtension
variable {R : Type v} [CommRing R]
variable {P M N : Type*}
  [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
variable (u : P →ₗ[R] M) (d : M →ₗ[R] N)

/-- Changing a coefficient module by an actual linear equivalence preserves exactness. -/
lemma exact_of_equiv {A B : Type v} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (e : A ≃ₗ[R] B)
    (hA : Function.Exact (u.lTensor A) (d.lTensor A)) :
    Function.Exact (u.lTensor B) (d.lTensor B) := by
  intro x
  constructor
  · intro hx
    have he : d.lTensor A ((e.symm.rTensor M) x) = 0 := by
      rw [show (e.symm.rTensor M) x = e.symm.toLinearMap.rTensor M x from rfl,
        differential_naturality, hx, map_zero]
    obtain ⟨a, ha⟩ := (hA _).mp he
    refine ⟨(e.rTensor P) a, ?_⟩
    change u.lTensor B (e.toLinearMap.rTensor P a) = x
    rw [differential_naturality, ha]
    exact (e.rTensor M).apply_symm_apply x
  · rintro ⟨a, rfl⟩
    apply (e.symm.rTensor N).injective
    change e.symm.toLinearMap.rTensor N (d.lTensor B (u.lTensor B a)) = _
    rw [← differential_naturality d, ← differential_naturality u,
      hA.apply_apply_eq_zero, map_zero]

/-- Exactness for simple coefficients extends through every finite composition series. -/
theorem exact_of_finiteLength [Module.Flat R N] (hdu : d.comp u = 0)
    (hS : ∀ (A : Type v) [AddCommGroup A] [Module R A] [IsSimpleModule R A],
      Function.Exact (u.lTensor A) (d.lTensor A))
    {B : Type v} [AddCommGroup B] [Module R B] (hB : IsFiniteLength R B) :
    Function.Exact (u.lTensor B) (d.lTensor B) := by
  induction hB with
  | of_subsingleton =>
    intro x
    exact ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ Subsingleton.elim _ _⟩
  | @of_simple_quotient B _ _ L _ _ ih =>
    exact exact_of_submodule u d hdu L ih (hS (B ⧸ L))

/-- Residue-field quotients supply all the simple coefficients, with no chosen bases. -/
theorem exact_of_residue_quotients [Module.Flat R N] (hdu : d.comp u = 0)
    (hres : ∀ (I : Ideal R) [I.IsMaximal],
      Function.Exact (u.lTensor (R ⧸ I)) (d.lTensor (R ⧸ I)))
    {B : Type v} [AddCommGroup B] [Module R B] (hB : IsFiniteLength R B) :
    Function.Exact (u.lTensor B) (d.lTensor B) := by
  apply exact_of_finiteLength u d hdu _ hB
  intro A _ _ hA
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hA
  let _ := hI
  exact exact_of_equiv u d e.symm (hres I)

end FLT.Mazur.TensorKernelFiniteLength
