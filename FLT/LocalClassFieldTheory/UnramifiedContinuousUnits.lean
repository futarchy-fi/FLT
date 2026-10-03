/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralUnitInvariantCohomology
public import FLT.LocalClassFieldTheory.UnramifiedOpenStages

/-!
# Continuous acyclicity of unramified integral units

The coefficients are the actual integral units of the unramified union, with
the discrete topology and restricted Galois action. Their invariant stages
are identified with canonical finite-stage units. Cofinality and the proved
continuous cohomology colimit then give vanishing in every positive degree.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory Limits

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]

local notation "U" => maximalUnramified R K C
local notation "G" => Gal(U/K)
local notation "M" => IntegralUnitModule R U

attribute [local instance] unramifiedUnionGalois integralUnitAction

/-- Discrete topology on the integral-unit coefficient group. -/
local instance unramifiedUnitTopology : TopologicalSpace M := ⊥
local instance unramifiedUnitDiscrete : DiscreteTopology M := ⟨rfl⟩

/-- A constructed invariant stage is the ordinary cohomology of its canonical integral units. -/
def unramifiedInvariantUnitCohomologyIso (n : UnramifiedIndex) (i : ℕ) :
    (invariantStageCohomologyDiagram ℤ G M i).obj (unramifiedOpenStage R K C n) ≅
      groupCohomology (integralUnitRep R (integralClosure R (unramifiedFiniteStage R K C n))
        K (unramifiedFiniteStage R K C n)) i :=
  integralUnitInvariantCohomologyIso R K U
    (unramifiedFiniteStage R K C n).toIntermediateField i

/-- Each constructed invariant stage has zero positive unit cohomology. -/
theorem unramifiedInvariantUnitCohomology_isZero (n : UnramifiedIndex) (i : ℕ) :
    IsZero ((invariantStageCohomologyDiagram ℤ G M (i + 1)).obj
      (unramifiedOpenStage R K C n)) :=
  (unramifiedFiniteStage_unit_cohomology_isZero R K C n i).of_iso
    (unramifiedInvariantUnitCohomologyIso R K C n (i + 1))

/-- The full invariant-stage colimit vanishes, using refinement to constructed stages. -/
theorem unramifiedUnitCohomologyColimit_isZero (i : ℕ) :
    IsZero (colimit (invariantStageCohomologyDiagram ℤ G M (i + 1))) := by
  let D := invariantStageCohomologyDiagram ℤ G M (i + 1)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply colimit.hom_ext
  intro N
  obtain ⟨n, hn⟩ := exists_unramifiedOpenStage_le R K C (OrderDual.ofDual N)
  let f : N ⟶ OrderDual.toDual (unramifiedOpenStage R K C n) := homOfLE hn
  have hz := unramifiedInvariantUnitCohomology_isZero R K C n i
  have hι : colimit.ι D N = 0 := by
    rw [← colimit.w D f]
    have hleg : colimit.ι D (OrderDual.toDual (unramifiedOpenStage R K C n)) = 0 :=
      hz.eq_of_src _ _
    rw [hleg, comp_zero]
  change colimit.ι D N ≫ 𝟙 _ = colimit.ι D N ≫ 0
  rw [hι, zero_comp, zero_comp]

/-- Integral units of the unramified union have zero continuous cohomology in positive degree. -/
theorem unramifiedContinuousUnitCohomology_isZero (i : ℕ) :
    IsZero (continuousCohomology ℤ G M (i + 1)) :=
  (unramifiedUnitCohomologyColimit_isZero R K C i).of_iso
    (continuousCohomologyColimitIso ℤ G M (i + 1)).symm

end LocalClassFieldTheory
