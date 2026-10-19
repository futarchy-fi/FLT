/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryTestValuations

/-!
# Fixed finite generator poles for original scalar rank-test obstructions

Choose generators once on each of the finitely many full principal test
charts. With matching exact fibers, an excluded scalar prime constructs a
pole among these generators at that exact prime. Regularity supplies a full
scalar power denominator, retaining nilpotents and the original scalar ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
open SchemeScalarPrincipalNeighborhood AffineValuationGeneratorLift
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryProduct boundaryCoordinate
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T) (hs : s.FiniteType)

/-- Fixed finite scalar generators for a full principal test chart. -/
def boundaryTestChartGenerators (t : B) :
    Finset Γ((boundaryTestChart s κ t).toScheme, ⊤) :=
  (boundaryTestChart_exists_generators s κ t hs).choose

/-- The generators are over the original boundary scalars, independently of any selected prime. -/
theorem boundaryTestChartGenerators_generate (t : B) :
    Subring.closure (Set.range (boundaryTestChartScalar s κ t) ∪
      (boundaryTestChartGenerators s κ hs t : Set _)) = ⊤ :=
  (boundaryTestChart_exists_generators s κ t hs).choose_spec

variable (a : Finset B)
local notation "σ" t => boundaryTestChartScalar s κ t
local notation "gens" t => boundaryTestChartGenerators s κ hs t
local notation "φ" t => scalarMorphism (σ t)

/-- An excluded prime with matching exact fiber has a pole among fixed finite chart generators. -/
theorem boundaryTestChart_exists_generator_pole (P : PrimeSpectrum T)
    (hf : ∀ z : boundaryProduct s κ, boundaryScalarProjection s κ z = P →
      ∀ t ∈ a, t ∈ (boundaryProjection s κ z).asIdeal)
    (hp : P ∉ boundaryScalarNilpotenceOpen s κ a) :
    ∃ (t : a) (S : ValuativeCommSq (φ t.val)), S.i₂ (closedPoint S.R) = P ∧
      ∃ b ∈ gens t.val, genericCoordinates (σ t.val) S b ∉ (algebraMap S.R S.K).range := by
  obtain ⟨t, S, hc⟩ := (boundaryTestChart_square_iff s κ a P).mpr hp
  refine ⟨t, S, hc, ?_⟩
  exact exists_generator_pole (σ t.val) (gens t.val)
    (boundaryTestChartGenerators_generate s κ hs t.val) S
    (boundaryTestChart_no_lift s κ a P hf t S hc)

/-- At a matching fiber, fixed-generator regularity is precisely original scalar coverage. -/
theorem boundaryScalar_mem_iff_test_generators_regular (P : PrimeSpectrum T)
    (hf : ∀ z : boundaryProduct s κ, boundaryScalarProjection s κ z = P →
      ∀ t ∈ a, t ∈ (boundaryProjection s κ z).asIdeal) :
    P ∈ boundaryScalarNilpotenceOpen s κ a ↔
      ∀ (t : a) (S : ValuativeCommSq (φ t.val)), S.i₂ (closedPoint S.R) = P →
        ∀ b ∈ gens t.val, genericCoordinates (σ t.val) S b ∈ (algebraMap S.R S.K).range := by
  constructor
  · intro hp t S hc
    exact False.elim (boundaryTestChart_square_excludes s κ a P t S hc hp)
  · intro hg
    apply boundaryScalar_mem_of_testChart_lifts s κ a P hf
    intro t S hc
    exact hasLift_of_generators (σ t.val) (gens t.val)
      (boundaryTestChartGenerators_generate s κ hs t.val) S (hg t S hc)

/-- Fixed-generator regularity constructs an avoiding scalar annihilating one whole test power. -/
theorem boundaryTestChart_denominator_of_regular (P : PrimeSpectrum T)
    (hf : ∀ z : boundaryProduct s κ, boundaryScalarProjection s κ z = P →
      ∀ t ∈ a, t ∈ (boundaryProjection s κ z).asIdeal)
    (hg : ∀ (t : a) (S : ValuativeCommSq (φ t.val)), S.i₂ (closedPoint S.R) = P →
      ∀ b ∈ gens t.val, genericCoordinates (σ t.val) S b ∈ (algebraMap S.R S.K).range) :
    ∃ (order : ℕ) (x : T), x ∉ P.asIdeal ∧
      boundaryScalarHom s κ x ∈ ((boundaryTestIdeal s κ a) ^ order).annihilator :=
  (mem_boundaryScalarNilpotenceOpen s κ a P).mp
    ((boundaryScalar_mem_iff_test_generators_regular s κ hs a P hf).mpr hg)

end FLT.Mazur.AffineScalarBoundaryNilpotence
