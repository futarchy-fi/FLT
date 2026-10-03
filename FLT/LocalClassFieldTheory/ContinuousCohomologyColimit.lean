/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousCochainColimit
public import FLT.LocalClassFieldTheory.FilteredHomologyDescent

/-!
# Continuous cohomology as a filtered colimit

The cohomology of the continuous inhomogeneous complex is the filtered
colimit of the cohomologies of the finite quotient complexes with invariant
coefficients. Boundary detection is proved, not required as an input.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open CategoryTheory Limits HomologicalComplex

variable (k G M : Type u) [CommRing k] [Group G] [AddCommGroup M] [Module k M]
  [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M]

/-- The continuous cohomology module is the homology of the continuous complex. -/
def continuousCohomology (n : ℕ) : ModuleCat k := (continuousCochains k G M).homology n

/-- The diagram consists of the actual cohomology modules of the finite quotients. -/
def invariantStageCohomologyDiagram (n : ℕ) : (OpenNormalSubgroup G)ᵒᵈ ⥤ ModuleCat k :=
  invariantStageDiagram k G M ⋙ homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n

/-- Inflation induces the comparison cocone on cohomology. -/
def continuousCohomologyCocone (n : ℕ) : Cocone (invariantStageCohomologyDiagram k G M n) :=
  (homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n).mapCocone (continuousStageCocone k G M)

/-- Continuous cohomology has the finite-stage filtered colimit universal property. -/
def continuousCohomologyIsColimit (n : ℕ) : IsColimit (continuousCohomologyCocone k G M n) := by
  apply isColimitOfReflects (forget (ModuleCat k))
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨N, y, hy⟩ := complexCocone_homology_surjective
      (invariantStageDiagram k G M) (continuousStageCocone k G M)
      (continuousStageInflation_injective k G M)
      (continuousStageInflation_jointly_surjective k G M) n x
    exact ⟨N, y, hy.symm⟩
  · intro N x y h
    exact complexCocone_homology_eq
      (invariantStageDiagram k G M) (continuousStageCocone k G M)
      (continuousStageInflation_injective k G M)
      (continuousStageInflation_jointly_surjective k G M) n N x y h

/-- The canonical filtered colimit is isomorphic to continuous cohomology. -/
def continuousCohomologyColimitIso (n : ℕ) :
    colimit (invariantStageCohomologyDiagram k G M n) ≅ continuousCohomology k G M n :=
  (colimit.isColimit _).coconePointUniqueUpToIso (continuousCohomologyIsColimit k G M n)

end LocalClassFieldTheory
