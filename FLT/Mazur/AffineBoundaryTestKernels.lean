/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryPrincipalTestCharts
public import FLT.Mazur.ScalarTestKernelProducts

/-!
# Exact scalar equation ideals on the full boundary test atlas

The actual scalar map on a principal test chart has the power-annihilation
kernel computed algebraically. A finite product of these ideals defines the
entire closed scalar obstruction and supplies unchanged scalar denominators.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
open ScalarTestLocalization ScalarLocalizedIdealNilpotence
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryProduct boundaryCoordinate
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T)
set_option quotPrecheck false
local notation "C" => Γ(boundaryProduct s κ, ⊤)
local notation "σ" => boundaryScalarHom s κ
local notation "coord" => boundaryCoordinate s κ

/-- Exact scalar equations on the full principal boundary chart. -/
def boundaryTestKernel (t : B) : Ideal T := RingHom.ker (boundaryTestChartScalar s κ t)

/-- The actual chart kernel is computed by localization of the unchanged product coordinates. -/
theorem boundaryTestKernel_eq (t : B) :
    boundaryTestKernel s κ t = testKernel σ (coord t) := by
  let j := (boundaryTestChart s κ t).ι
  let _ := j.appTop.hom.toAlgebra
  let _ : IsLocalization.Away (coord t) Γ((boundaryTestChart s κ t).toScheme, ⊤) := by
    dsimp only [boundaryTestChart, j]
    infer_instance
  ext x
  rw [mem_testKernel]
  change algebraMap C Γ((boundaryTestChart s κ t).toScheme, ⊤) (σ x) = 0 ↔ _
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers (coord t))]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨k, hk⟩ := u.property
    exact ⟨k, by simpa only [hk] using hu⟩
  · rintro ⟨k, hk⟩
    exact ⟨⟨coord t ^ k, ⟨k, rfl⟩⟩, hk⟩

/-- Exact chart equations retain all nilpotents of the original boundary product. -/
theorem mem_boundaryTestKernel (t : B) (x : T) :
    x ∈ boundaryTestKernel s κ t ↔ ∃ k : ℕ, coord t ^ k * σ x = 0 := by
  rw [boundaryTestKernel_eq, mem_testKernel]

variable (a : Finset B)
local notation "I" => boundaryTestIdeal s κ a

/-- A finite product of actual chart kernels, in the original scalar ring. -/
def boundaryTestKernelProduct : Ideal T := ∏ t ∈ a, boundaryTestKernel s κ t

/-- Scalar coverage is exactly avoidance by every actual principal test-chart kernel. -/
theorem boundaryScalar_mem_iff_testKernels (P : PrimeSpectrum T) :
    P ∈ boundaryScalarNilpotenceOpen s κ a ↔
      ∀ t ∈ a, ¬ boundaryTestKernel s κ t ≤ P.asIdeal := by
  classical
  change P ∈ scalarNilpotenceOpen σ (Ideal.span (coord '' (a : Set B))) ↔ _
  rw [← Finset.coe_image]
  rw [mem_scalarNilpotenceOpen_iff_kernels]
  simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  simp only [boundaryTestKernel_eq]

/-- The exact original scalar obstruction is defined by one finite product ideal. -/
theorem boundaryScalar_mem_iff_testKernelProduct (P : PrimeSpectrum T) :
    P ∈ boundaryScalarNilpotenceOpen s κ a ↔
      ¬ boundaryTestKernelProduct s κ a ≤ P.asIdeal := by
  rw [boundaryScalar_mem_iff_testKernels, boundaryTestKernelProduct, P.isPrime.prod_le]
  push Not
  rfl

/-- This closed equation includes all components with centers generizing the selected prime. -/
theorem boundaryScalar_compl_testKernelProduct :
    (boundaryScalarNilpotenceOpen s κ a : Set (PrimeSpectrum T))ᶜ =
      PrimeSpectrum.zeroLocus (boundaryTestKernelProduct s κ a : Set T) := by
  ext P
  simpa only [Set.mem_compl_iff, SetLike.mem_coe, PrimeSpectrum.mem_zeroLocus,
    SetLike.coe_subset_coe, not_not] using
    not_congr (boundaryScalar_mem_iff_testKernelProduct s κ a P)

/-- Simultaneous actual chart equations kill a whole power without changing the chosen scalar. -/
theorem boundary_power_annihilator_iff_testKernels (x : T) :
    (∃ k : ℕ, σ x ∈ (I ^ k).annihilator) ↔
      ∀ t ∈ a, x ∈ boundaryTestKernel s κ t := by
  classical
  change (∃ k : ℕ, σ x ∈ ((Ideal.span (coord '' (a : Set B))) ^ k).annihilator) ↔ _
  rw [← Finset.coe_image, exists_power_annihilator_iff_kernels]
  simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  simp only [boundaryTestKernel_eq]

/-- The product of independently chosen chart equations is an explicit common scalar. -/
theorem boundary_product_chart_equations (P : PrimeSpectrum T) (x : B → T)
    (hx : ∀ t ∈ a, x t ∉ P.asIdeal)
    (he : ∀ t ∈ a, x t ∈ boundaryTestKernel s κ t) :
    (∏ t ∈ a, x t) ∉ P.asIdeal ∧
      ∃ k : ℕ, σ (∏ t ∈ a, x t) ∈ (I ^ k).annihilator := by
  constructor
  · intro hp
    obtain ⟨t, ht, hm⟩ := Ideal.IsPrime.prod_mem_iff.mp hp
    exact hx t ht hm
  · apply (boundary_power_annihilator_iff_testKernels s κ a _).mpr
    intro t ht
    exact (Ideal.prod_le_inf.trans (Finset.inf_le ht)) (Ideal.prod_mem_prod he)

end FLT.Mazur.AffineScalarBoundaryNilpotence
