/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryTestKernels
public import FLT.Mazur.ScalarTestKernelDescent
public import FLT.Mazur.ScalarTestResidualSeparation
public import FLT.Mazur.SchemeFppfCoverInvariantFunctions

/-!
# Computing original boundary scalar equations on a finite fppf cover

Full coefficient rings of a finite fppf cover compute the exact chart kernels.
The cover can be used to construct scalar equations independently on its
branches; finite descent supplies an original scalar power certificate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
open ScalarTestLocalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryProduct boundaryCoordinate
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T)
  (C : Scheme.Cover.{0} Scheme.fppfPrecoverage (boundaryProduct s κ)) [Finite C.I₀]
local notation "σ" => boundaryScalarHom s κ
local notation "coord" => boundaryCoordinate s κ
set_option quotPrecheck false
local notation "g" i:max => (C.f i).appTop.hom

/-- Actual finite fppf branches compute the exact original principal-chart scalar kernel. -/
theorem boundaryTestKernel_eq_fppf (t : B) :
    boundaryTestKernel s κ t = ⨅ i, testKernel ((g i).comp σ) ((g i) (coord t)) := by
  rw [boundaryTestKernel_eq]
  exact testKernel_eq_iInf_cover σ (fun i ↦ g i)
    (fun _ _ h ↦ SchemeFppfFamily.cover_sections_ext C h) (coord t)

/-- Branch equations descend with a constructed common exponent and the same original scalar. -/
theorem boundaryTestKernel_fppf_power (t : B) (x : T)
    (h : ∀ i, ∃ k : ℕ, ((g i) (coord t)) ^ k * (g i) (σ x) = 0) :
    ∃ k : ℕ, coord t ^ k * σ x = 0 := by
  apply exists_uniform_test_power σ (fun i ↦ g i)
    (fun _ _ he ↦ SchemeFppfFamily.cover_sections_ext C he) (coord t) x
  intro i
  exact (mem_testKernel ((g i).comp σ) ((g i) (coord t)) x).mpr (h i)

/-- Avoidance descends from independent equations on the full finite covering rings. -/
theorem boundaryTestKernel_not_le_iff_fppf (t : B) (P : PrimeSpectrum T) :
    ¬ boundaryTestKernel s κ t ≤ P.asIdeal ↔
      ∀ i, ¬ testKernel ((g i).comp σ) ((g i) (coord t)) ≤ P.asIdeal := by
  rw [boundaryTestKernel_eq]
  exact testKernel_not_le_iff_cover σ (fun i ↦ g i)
    (fun _ _ h ↦ SchemeFppfFamily.cover_sections_ext C h) (coord t) P

/-- Independent original scalar equations on each finite branch yield full scalar rank coverage. -/
theorem boundaryScalar_mem_of_fppf_equations (a : Finset B) (P : PrimeSpectrum T)
    (h : ∀ t ∈ a, ∀ i, ∃ (x : T) (k : ℕ), x ∉ P.asIdeal ∧
      ((g i) (coord t)) ^ k * (g i) (σ x) = 0) :
    P ∈ boundaryScalarNilpotenceOpen s κ a := by
  apply (boundaryScalar_mem_iff_testKernels s κ a P).mpr
  intro t ht
  apply (boundaryTestKernel_not_le_iff_fppf s κ C t P).mpr
  intro i hle
  obtain ⟨x, k, hx, he⟩ := h t ht i
  exact hx (hle ((mem_testKernel ((g i).comp σ) ((g i) (coord t)) x).mpr ⟨k, he⟩))

/-- Finite fppf equation descent produces a whole-power certificate in the unchanged scalar ring. -/
theorem boundaryScalar_denominator_of_fppf_equations (a : Finset B) (P : PrimeSpectrum T)
    (h : ∀ t ∈ a, ∀ i, ∃ (x : T) (k : ℕ), x ∉ P.asIdeal ∧
      ((g i) (coord t)) ^ k * (g i) (σ x) = 0) :
    ∃ (order : ℕ) (x : T), x ∉ P.asIdeal ∧
      σ x ∈ ((boundaryTestIdeal s κ a) ^ order).annihilator :=
  (mem_boundaryScalarNilpotenceOpen s κ a P).mp
    (boundaryScalar_mem_of_fppf_equations s κ C a P h)

omit C [Finite C.I₀] in
/-- Whole residual coverage constructs one scalar equal to one modulo its defining ideal. -/
theorem boundaryScalar_residual_uniform_denominator (a : Finset B) (J : Ideal T)
    (h : ∀ P : PrimeSpectrum T, J ≤ P.asIdeal →
      P ∈ boundaryScalarNilpotenceOpen s κ a) :
    ∃ (x : T) (order : ℕ), 1 - x ∈ J ∧
      σ x ∈ ((boundaryTestIdeal s κ a) ^ order).annihilator ∧
      ∀ P : PrimeSpectrum T, J ≤ P.asIdeal → x ∉ P.asIdeal := by
  classical
  have h' : ∀ P : PrimeSpectrum T, J ≤ P.asIdeal →
      P ∈ ScalarLocalizedIdealNilpotence.scalarNilpotenceOpen σ
        (Ideal.span ((a.image coord : Finset _) : Set _)) := by
    simpa only [boundaryScalarNilpotenceOpen, boundaryTestIdeal, Finset.coe_image] using h
  obtain ⟨x, order, hx, he, hp, _⟩ :=
    residual_uniform_power_neighborhood σ (a.image coord) J h'
  refine ⟨x, order, hx, ?_, hp⟩
  simpa only [boundaryTestIdeal, Finset.coe_image] using he

end FLT.Mazur.AffineScalarBoundaryNilpotence
