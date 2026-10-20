/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicPrescribedBoundary
public import FLT.Mazur.IntegralOneGonBoundaryLevels

/-!
# Actual complete-base ample cyclic levels and prescribed boundary classes

The constructed subgroup supplies an ample cyclic moduli object on the
genuine degeneration. Every prescribed original one-gon subgroup class is
its actual arithmetic boundary pullback, including in characteristics dividing n.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open GeneralizedEllipticCurve.FiniteSubgroup CharacterSchemeBaseChange

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]

/-- The genuine nonconstant complete-base family with its constructed ample cyclic subgroup. -/
def canonicalLevel : ampleCyclicLevels (Spec (.of R)) n :=
  ⟨⟨_, canonicalFiniteSubgroup I t ht n⟩, canonicalFiniteSubgroup_isCyclic I t ht n,
    canonicalFiniteSubgroup_isAmple_unrestricted I t ht n⟩

/-- Its class retains the original family and the actual full canonical subgroup. -/
def canonicalLevelClass : ampleCyclicClasses (Spec (.of R)) n :=
  Quotient.mk _ (canonicalLevel I t ht n)

variable (K : Type) [Field K] [Algebra R K] (hzero : algebraMap R K t = 0)
  (H : (PolygonGeneralizedCurve.curve K 1 Nat.zero_lt_one
    (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
    (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)).FiniteSubgroup n)

include hzero in
/-- The actual complete-base class pulls back to any prescribed original one-gon subgroup. -/
theorem canonicalLevelClass_boundary (hc : H.IsCyclic) (ha : H.IsAmple) :
    ampleCyclicClassesPullback (baseMap R K) n (canonicalLevelClass I t ht n) =
      Quotient.mk _ (⟨⟨_, H⟩, hc, ha⟩ : ampleCyclicLevels (Spec (.of K)) n) :=
  Quotient.sound ⟨(prescribedBoundaryIso I t ht n K hzero H).symm⟩

include H hzero in
/-- Boundary comparison with the earlier arithmetic model retains the entire moduli class. -/
theorem canonicalLevelClass_boundary_arithmetic :
    ampleCyclicClassesPullback (baseMap R K) n (canonicalLevelClass I t ht n) =
      ampleCyclicClassesPullback (baseMap R K) n
        (Quotient.mk _ (ArithmeticOneGonOriginalRoots.level n R)) := by
  have hc := ArithmeticOneGonArbitrarySubgroupPullback.original_isCyclic K H
  have ha := ArithmeticOneGonArbitrarySubgroupPullback.original_isAmple K H
  exact (canonicalLevelClass_boundary I t ht n K hzero H hc ha).trans
    (ArithmeticOneGonArbitrarySubgroupPullback.level_class R K H hc ha).symm

/-- The integral power-series degeneration with its actual canonical ample cyclic level. -/
def integralCanonicalLevelClass : ampleCyclicClasses (Spec (.of (PowerSeries ℤ))) n :=
  canonicalLevelClass (PolygonInfinitesimalStages.parameterIdeal ℤ) PowerSeries.X
    (Ideal.subset_span (Set.mem_singleton _)) n

/-- Every prescribed original one-gon class is a boundary of the genuine integral degeneration. -/
theorem integralCanonicalLevelClass_boundary (hc : H.IsCyclic) (ha : H.IsAmple) :
    ampleCyclicClassesPullback (IntegralOneGonSpecializations.boundaryMap K) n
        (integralCanonicalLevelClass n) =
      Quotient.mk _ (⟨⟨_, H⟩, hc, ha⟩ : ampleCyclicLevels (Spec (.of K)) n) := by
  let _ := (IntegralOneGonSpecializations.boundaryHom K).toAlgebra
  exact canonicalLevelClass_boundary _ _ _ n K
    (IntegralOneGonSpecializations.boundaryHom_parameter K) H hc ha

end FLT.Mazur.OneGonAdicCharacterTower
