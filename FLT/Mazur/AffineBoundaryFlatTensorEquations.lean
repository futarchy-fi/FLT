/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryTestKernels
public import FLT.Mazur.FlatScalarTestDenominators
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Exact flat scalar equations on the full boundary coordinate algebra

Use the full tensor product of the original boundary coordinates. Flat
scalar extension preserves its principal-test kernel ideals and descends
power equations without changing individual exponents. Finite presentation
of the scalar extension is unnecessary.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
open ScalarTestLocalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryProduct boundaryCoordinate
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T)
set_option quotPrecheck false
local notation "C" => Γ(boundaryProduct s κ, ⊤)
local notation "σ" => boundaryScalarHom s κ
/-- The unchanged scalar map equips the full boundary coordinates with their scalar algebra. -/
local instance boundaryTensorAlgebra : Algebra T C := (σ).toAlgebra
variable (S : Type) [CommRing S] [Algebra T S]
local notation "C'" => S ⊗[T] C
local notation "j" => Algebra.TensorProduct.includeRight (R := T) (A := S) (B := C)

/-- An exact equation on the full scalar extension, with its branch scalar and exponent. -/
def boundaryTensorPowerEquation (t : B) (x : S) (k : ℕ) : Prop :=
  (j (boundaryCoordinate s κ t)) ^ k * algebraMap S C' x = 0

/-- Scalar equations on a full tensor-product principal test chart. -/
def boundaryTensorTestKernel (t : B) : Ideal S :=
  testKernel (algebraMap S C') (j (boundaryCoordinate s κ t))

/-- The tensor chart kernel records actual power equations, not equations after reduction. -/
theorem mem_boundaryTensorTestKernel (t : B) (x : S) :
    x ∈ boundaryTensorTestKernel s κ S t ↔
      ∃ k : ℕ, boundaryTensorPowerEquation s κ S t x k :=
  mem_testKernel _ _ _

variable [Module.Flat T S]

/-- The actual full tensor test kernel is exactly the extended original chart kernel. -/
theorem boundaryTensorTestKernel_eq (t : B) :
    boundaryTensorTestKernel s κ S t =
      (boundaryTestKernel s κ t).map (algebraMap T S) := by
  unfold boundaryTensorTestKernel
  rw [testKernel_flat_baseChange, boundaryTestKernel_eq]
  rfl

/-- A branch power equation produces an original equation at the same exponent. -/
theorem boundary_original_equation_same_power (Q : PrimeSpectrum S) (t : B)
    (x : S) (k : ℕ) (hx : x ∉ Q.asIdeal)
    (he : boundaryTensorPowerEquation s κ S t x k) :
    ∃ r : T, r ∉ Q.asIdeal.comap (algebraMap T S) ∧
      boundaryCoordinate s κ t ^ k * boundaryScalarHom s κ r = 0 :=
  FlatScalarPowerKernel.original_equation_same_power S Q (boundaryCoordinate s κ t) k x hx he

/-- Arbitrary flat branch equations cover the original scalar prime without finite presentation. -/
theorem boundaryScalar_mem_of_flat_tensor_equations (a : Finset B) (Q : PrimeSpectrum S)
    (h : ∀ t ∈ a, ∃ (x : S) (k : ℕ), x ∉ Q.asIdeal ∧
      boundaryTensorPowerEquation s κ S t x k) :
    PrimeSpectrum.comap (algebraMap T S) Q ∈ boundaryScalarNilpotenceOpen s κ a := by
  apply (boundaryScalar_mem_iff_testKernels s κ a _).mpr
  intro t ht hle
  obtain ⟨x, k, hx, he⟩ := h t ht
  obtain ⟨r, hr, hm⟩ := boundary_original_equation_same_power s κ S Q t x k hx he
  exact hr (hle ((mem_boundaryTestKernel s κ t r).mpr ⟨k, hm⟩))

/-- These equations construct one original scalar killing a whole power of the full test ideal. -/
theorem boundary_denominator_of_flat_tensor_equations (a : Finset B) (Q : PrimeSpectrum S)
    (h : ∀ t ∈ a, ∃ (x : S) (k : ℕ), x ∉ Q.asIdeal ∧
      boundaryTensorPowerEquation s κ S t x k) :
    ∃ (k : ℕ) (r : T), r ∉ Q.asIdeal.comap (algebraMap T S) ∧
      boundaryScalarHom s κ r ∈ ((boundaryTestIdeal s κ a) ^ k).annihilator :=
  (mem_boundaryScalarNilpotenceOpen s κ a _).mp
    (boundaryScalar_mem_of_flat_tensor_equations s κ S a Q h)

omit [Module.Flat T S] in
/-- Faithful flatness constructs a branch prime; no prime lifting is supplied as input. -/
theorem boundaryScalar_mem_of_faithfully_flat_tensor [Module.FaithfullyFlat T S]
    (a : Finset B) (P : PrimeSpectrum T)
    (h : ∀ Q : PrimeSpectrum S, PrimeSpectrum.comap (algebraMap T S) Q = P →
      ∀ t ∈ a, ∃ (x : S) (k : ℕ), x ∉ Q.asIdeal ∧
        boundaryTensorPowerEquation s κ S t x k) :
    P ∈ boundaryScalarNilpotenceOpen s κ a := by
  obtain ⟨Q, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := T) (B := S) P
  rw [← hQ]
  exact boundaryScalar_mem_of_flat_tensor_equations s κ S a Q (h Q hQ)

omit [Module.Flat T S] in
/-- Each test may independently choose an arbitrary flat scalar algebra and a point over P. -/
theorem boundaryScalar_mem_of_independent_flat_tensor (a : Finset B)
    (Ss : a → Type) [∀ t, CommRing (Ss t)] [∀ t, Algebra T (Ss t)]
    [∀ t, Module.Flat T (Ss t)] (P : PrimeSpectrum T) (Qs : ∀ t, PrimeSpectrum (Ss t))
    (hQ : ∀ t, PrimeSpectrum.comap (algebraMap T (Ss t)) (Qs t) = P)
    (h : ∀ t, ∃ (x : Ss t) (k : ℕ), x ∉ (Qs t).asIdeal ∧
      boundaryTensorPowerEquation s κ (Ss t) t.val x k) :
    P ∈ boundaryScalarNilpotenceOpen s κ a := by
  apply (boundaryScalar_mem_iff_testKernels s κ a P).mpr
  intro t ht hle
  obtain ⟨x, k, hx, he⟩ := h ⟨t, ht⟩
  obtain ⟨r, hr, hm⟩ :=
    boundary_original_equation_same_power s κ (Ss ⟨t, ht⟩) (Qs ⟨t, ht⟩) t x k hx he
  apply hr
  change r ∈ (PrimeSpectrum.comap (algebraMap T (Ss ⟨t, ht⟩)) (Qs ⟨t, ht⟩)).asIdeal
  rw [hQ]
  exact hle ((mem_boundaryTestKernel s κ t r).mpr ⟨k, hm⟩)

end FLT.Mazur.AffineScalarBoundaryNilpotence
