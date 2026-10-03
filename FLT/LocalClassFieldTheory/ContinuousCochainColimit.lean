/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousStageDiagram
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Continuous cochains are the filtered colimit of finite-stage complexes

Every continuous cochain descends. Equality is detected by injective inflation.
These facts prove the colimit universal property, first degreewise and then
in the category of complexes.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open CategoryTheory Limits

variable (k G M : Type u) [CommRing k] [Group G] [AddCommGroup M] [Module k M]
  [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M]

/-- The trivial quotient supplies an index even before any cochain is chosen. -/
instance invariantStageIndexNonempty : Nonempty (OpenNormalSubgroup G)ᵒᵈ :=
  ⟨OrderDual.toDual ⟨(⊤ : OpenSubgroup G), by change (⊤ : Subgroup G).Normal; infer_instance⟩⟩

/-- In each degree, continuous cochains satisfy the module colimit universal property. -/
def continuousCochainIsColimit (n : ℕ) :
    IsColimit ((HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℕ) n).mapCocone
      (continuousStageCocone k G M)) := by
  apply isColimitOfReflects (forget (ModuleCat k))
  apply Types.FilteredColimit.isColimitOf'
  · intro c
    obtain ⟨N, d, hd⟩ := continuousStageInflation_jointly_surjective k G M n c
    exact ⟨N, d, hd.symm⟩
  · intro N c d h
    have he := continuousStageInflation_injective k G M N n h
    exact ⟨N, 𝟙 N, congrArg _ he⟩

/-- The actual continuous complex is the filtered colimit of the quotient complexes. -/
def continuousCochainsIsColimit : IsColimit (continuousStageCocone k G M) :=
  HomologicalComplex.isColimitOfEval _ _ (continuousCochainIsColimit k G M)

/-- The canonical categorical colimit is isomorphic to the continuous complex. -/
def continuousCochainsColimitIso :
    colimit (invariantStageDiagram k G M) ≅ continuousCochains k G M :=
  (colimit.isColimit _).coconePointUniqueUpToIso (continuousCochainsIsColimit k G M)

end LocalClassFieldTheory
