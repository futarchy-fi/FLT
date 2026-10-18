/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeBadAffineCoverBoundaryUnits
public import FLT.Mazur.SchemeBadAffineCoverBoundaryWitness
public import FLT.Mazur.SchemeBadAffineCoverFiniteType
public import FLT.Mazur.SchemeValuationImageClosure
public import FLT.Mazur.AffineValuationGeneratorLift
public import FLT.Mazur.ValuationPoleReciprocal

/-!
# Valuative centers and finite poles on the actual bad charts

Every original boundary obstruction constructs a valuation square in the
same bad chart. An empty exact fiber forces a pole among its fixed finite
original-scalar generators. The original boundary prime is kept exactly.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing
namespace FLT.Mazur.SchemeBadAffineCover
open SchemeScalarPrincipalNeighborhood SchemeSpecializationValuation
open AffineValuationGeneratorLift
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R T : Type} [CommRing R] [CommRing T] {X : Scheme}
  [NoetherianSpace X] (s : R →+* Γ(X, ⊤)) (O : X.Opens) (κ : R →+* T)

/-- A boundary obstruction is exactly a valuative center of the same actual bad chart. -/
theorem mem_boundaryChart_range_iff_valuation (i : (badCover O).I₀) (P : PrimeSpectrum T) :
    P ∈ Set.range (boundaryChartObstructionι s O κ i) ↔
      ∃ S : ValuativeCommSq (scalarMorphism (badChartScalar s O i)),
        S.i₂ (closedPoint S.R) = PrimeSpectrum.comap κ P := by
  let _ : NoetherianSpace ((badCover O).X i) :=
    ((badCover O).f i).isOpenEmbedding.isInducing.noetherianSpace
  have he : P ∈ Set.range (boundaryChartObstructionι s O κ i) ↔
      PrimeSpectrum.comap κ P ∈
        closure (Set.range (scalarMorphism (badChartScalar s O i))) := by
    rw [badChart_scalar_image_closure, mem_boundaryChartObstruction_range_iff]
    rfl
  rw [he, mem_closure_range_iff_square]

/-- Any actual obstruction point produces the square, without postulating an extension. -/
theorem boundaryChart_point_has_valuation (i : (badCover O).I₀)
    (x : boundaryChartObstruction s O κ i) :
    ∃ S : ValuativeCommSq (scalarMorphism (badChartScalar s O i)),
      S.i₂ (closedPoint S.R) =
        PrimeSpectrum.comap κ (boundaryChartObstructionι s O κ i x) :=
  (mem_boundaryChart_range_iff_valuation s O κ i _).mp ⟨x, rfl⟩

/-- Every lift gives a bad point over the exact original scalar prime, not just a generization. -/
theorem boundaryChart_valuation_lift_point (i : (badCover O).I₀) (P : PrimeSpectrum T)
    (S : ValuativeCommSq (scalarMorphism (badChartScalar s O i)))
    (hcenter : S.i₂ (closedPoint S.R) = PrimeSpectrum.comap κ P)
    (h : S.commSq.HasLift) :
    ∃ y : X, y ∉ O ∧ scalarMorphism s y = PrimeSpectrum.comap κ P := by
  obtain ⟨l⟩ := (CommSq.HasLift.iff S.commSq).mp h
  let y := l.l (closedPoint S.R)
  have hy := (lift_specializes (scalarMorphism (badChartScalar s O i)) S l).2.trans hcenter
  change scalarMorphism (badChartScalar s O i) y = PrimeSpectrum.comap κ P at hy
  rw [badChartScalar, scalarMorphism_comp] at hy
  exact ⟨badChartMap O i y, badChartMap_not_mem O i y, hy⟩

/-- Completeness of the entire exact fiber prevents extension of an actual bad-chart square. -/
theorem boundaryChart_valuation_no_lift (i : (badCover O).I₀) (P : PrimeSpectrum T)
    (S : ValuativeCommSq (scalarMorphism (badChartScalar s O i)))
    (hcenter : S.i₂ (closedPoint S.R) = PrimeSpectrum.comap κ P)
    (hf : ∀ y : X, scalarMorphism s y = PrimeSpectrum.comap κ P → y ∈ O) :
    ¬ S.commSq.HasLift := by
  intro hl
  obtain ⟨y, hy, he⟩ := boundaryChart_valuation_lift_point s O κ i P S hcenter hl
  exact hy (hf y he)

variable (g : X ⟶ Spec (.of ℤ)) [LocallyOfFiniteType g]

/-- Exact-fiber tests force a finite generator pole on every remaining valuative obstruction. -/
theorem boundaryChart_valuation_generator_pole (i : (badCover O).I₀) (P : PrimeSpectrum T)
    (S : ValuativeCommSq (scalarMorphism (badChartScalar s O i)))
    (hcenter : S.i₂ (closedPoint S.R) = PrimeSpectrum.comap κ P)
    (hf : ∀ y : X, scalarMorphism s y = PrimeSpectrum.comap κ P → y ∈ O) :
    ∃ b ∈ badChartGenerators s O g i,
      genericCoordinates (badChartScalar s O i) S b ∉ (algebraMap S.R S.K).range :=
  exists_generator_pole (badChartScalar s O i) (badChartGenerators s O g i)
    (badChartGenerators_generate s O g i) S
    (boundaryChart_valuation_no_lift s O κ i P S hcenter hf)

/-- Finite generator regularity plus a whole exact-fiber test excludes a boundary obstruction. -/
theorem not_mem_boundaryChart_range_of_regular_generators (i : (badCover O).I₀)
    (P : PrimeSpectrum T)
    (hf : ∀ y : X, scalarMorphism s y = PrimeSpectrum.comap κ P → y ∈ O)
    (hg : ∀ S : ValuativeCommSq (scalarMorphism (badChartScalar s O i)),
      S.i₂ (closedPoint S.R) = PrimeSpectrum.comap κ P →
        ∀ b ∈ badChartGenerators s O g i,
          genericCoordinates (badChartScalar s O i) S b ∈ (algebraMap S.R S.K).range) :
    P ∉ Set.range (boundaryChartObstructionι s O κ i) := by
  intro h
  obtain ⟨S, hS⟩ := (mem_boundaryChart_range_iff_valuation s O κ i P).mp h
  obtain ⟨b, hb, hpole⟩ := boundaryChart_valuation_generator_pole s O κ g i P S hS hf
  exact hpole (hg S hS b hb)

/-- Every remaining obstruction has a finite generator and a reciprocal vanishing at its center. -/
theorem boundaryChart_point_has_reciprocal (i : (badCover O).I₀)
    (x : boundaryChartObstruction s O κ i)
    (hf : ∀ y : X, scalarMorphism s y =
      PrimeSpectrum.comap κ (boundaryChartObstructionι s O κ i x) → y ∈ O) :
    ∃ S : ValuativeCommSq (scalarMorphism (badChartScalar s O i)),
      S.i₂ (closedPoint S.R) =
        PrimeSpectrum.comap κ (boundaryChartObstructionι s O κ i x) ∧
      ∃ b ∈ badChartGenerators s O g i, ∃ v : S.R,
        residue S.R v = 0 ∧
          algebraMap S.R S.K v * genericCoordinates (badChartScalar s O i) S b = 1 := by
  obtain ⟨S, hS⟩ := boundaryChart_point_has_valuation s O κ i x
  obtain ⟨b, hb, hpole⟩ := boundaryChart_valuation_generator_pole s O κ g i _ S hS hf
  obtain ⟨v, hv, he⟩ := ValuationPoleReciprocal.exists_residue_zero_reciprocal
    S.R S.K _ hpole
  exact ⟨S, hS, b, hb, v, hv, he⟩

/-- Regularity tests on the finite actual chart generators supply original-prime avoidance. -/
theorem scalar_safe_of_regular_generators (P : PrimeSpectrum T)
    (hf : ∀ y : X, scalarMorphism s y = PrimeSpectrum.comap κ P → y ∈ O)
    (hg : ∀ (i : (badCover O).I₀)
      (S : ValuativeCommSq (scalarMorphism (badChartScalar s O i))),
      S.i₂ (closedPoint S.R) = PrimeSpectrum.comap κ P →
        ∀ b ∈ badChartGenerators s O g i,
          genericCoordinates (badChartScalar s O i) S b ∈ (algebraMap S.R S.K).range) :
    PrimeSpectrum.comap κ P ∈ scalarNeighborhoodLocus s O := by
  apply (scalar_safe_iff_boundaryChart_obstructions s O κ P).mpr
  exact fun i ↦ not_mem_boundaryChart_range_of_regular_generators s O κ g i P hf (hg i)

/-- Universal exact-fiber and finite regularity tests construct a finite original unit equation. -/
theorem boundary_equation_of_regular_generators
    (hf : ∀ (P : PrimeSpectrum T) (y : X),
      scalarMorphism s y = PrimeSpectrum.comap κ P → y ∈ O)
    (hg : ∀ (P : PrimeSpectrum T) (i : (badCover O).I₀)
      (S : ValuativeCommSq (scalarMorphism (badChartScalar s O i))),
      S.i₂ (closedPoint S.R) = PrimeSpectrum.comap κ P →
        ∀ b ∈ badChartGenerators s O g i,
          genericCoordinates (badChartScalar s O i) S b ∈ (algebraMap S.R S.K).range) :
    ∃ (n : ℕ) (a : Fin n → R) (b : Fin n → T),
      (∀ j, X.basicOpen (s (a j)) ≤ O) ∧ ∑ j, b j * κ (a j) = 1 := by
  apply (scalar_boundary_unit_ideal_iff_finite_equation s O κ).mp
  apply (scalar_boundary_cover_iff_unit_ideal s O κ).mp
  exact fun P ↦ scalar_safe_of_regular_generators s O κ g P (hf P) (hg P)

end FLT.Mazur.SchemeBadAffineCover
