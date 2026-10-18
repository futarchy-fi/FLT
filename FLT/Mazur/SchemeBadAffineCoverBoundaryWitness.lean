/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeBadAffineCoverBoundaryObstruction
public import FLT.Mazur.NoetherianClosedImageGenerizations

/-!
# Actual bad-chart witnesses for closed boundary obstructions

Every point of a closed boundary obstruction is witnessed by an actual point
of that same bad chart over a generization of the contracted boundary prime.
A finite set of chart points suffices for all boundary primes simultaneously.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeBadAffineCover
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R T : Type} [CommRing R] [CommRing T] {X : Scheme}
  [NoetherianSpace X] (s : R →+* Γ(X, ⊤)) (O : X.Opens) (κ : R →+* T)

local instance badChartNoetherian (i : (badCover O).I₀) :
    NoetherianSpace ((badCover O).X i) :=
  ((badCover O).f i).isOpenEmbedding.isInducing.noetherianSpace

/-- A finite list of actual points in one chart detects its entire scalar-image closure. -/
theorem exists_finite_boundaryChart_witnesses (i : (badCover O).I₀) :
    ∃ E : Set ((badCover O).X i), E.Finite ∧
      ∀ P : PrimeSpectrum T,
        P ∈ Set.range (boundaryChartObstructionι s O κ i) ↔
          ∃ x ∈ E, (scalarMorphism (badChartScalar s O i) x).asIdeal ≤ P.asIdeal.comap κ := by
  obtain ⟨E, hE, _, htest⟩ := NoetherianClosedImage.exists_finite_image_generizations
    (fun x ↦ (scalarMorphism (badChartScalar s O i) x : PrimeSpectrum R))
    (scalarMorphism (badChartScalar s O i)).continuous isClosed_univ
  refine ⟨E, hE, fun P ↦ ?_⟩
  have hp := htest (PrimeSpectrum.comap κ P)
  rw [Set.image_univ, badChart_scalar_image_closure] at hp
  rw [mem_boundaryChartObstruction_range_iff]
  exact hp.trans (by
    apply exists_congr
    intro x
    exact and_congr_right fun _ ↦ (PrimeSpectrum.le_iff_specializes _ _).symm)

/-- Any point of the closed obstruction has a genuine bad-chart generization witness. -/
theorem boundaryChart_point_has_bad_witness (i : (badCover O).I₀)
    (x : boundaryChartObstruction s O κ i) :
    ∃ y : (badCover O).X i,
      (scalarMorphism (badChartScalar s O i) y).asIdeal ≤
        (boundaryChartObstructionι s O κ i x).asIdeal.comap κ := by
  obtain ⟨E, _, hE⟩ := exists_finite_boundaryChart_witnesses s O κ i
  obtain ⟨y, _, hy⟩ := (hE _).mp ⟨x, rfl⟩
  exact ⟨y, hy⟩

/-- The witness remains an actual bad point of the original ambient scheme. -/
theorem boundaryChart_point_has_ambient_witness (i : (badCover O).I₀)
    (x : boundaryChartObstruction s O κ i) :
    ∃ y : X, y ∉ O ∧ (scalarMorphism s y).asIdeal ≤
      (boundaryChartObstructionι s O κ i x).asIdeal.comap κ := by
  obtain ⟨y, hy⟩ := boundaryChart_point_has_bad_witness s O κ i x
  refine ⟨badChartMap O i y, badChartMap_not_mem O i y, ?_⟩
  rw [badChartScalar, scalarMorphism_comp] at hy
  exact hy

end FLT.Mazur.SchemeBadAffineCover
