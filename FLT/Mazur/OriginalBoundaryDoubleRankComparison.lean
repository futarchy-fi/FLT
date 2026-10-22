/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryDoubleRankTests
public import FLT.Mazur.OriginalBoundaryFiniteComparisonTests

/-!
# The exact comparison on independent boundary rank stages

The full comparison is a finite closed immersion on every two-rank stage.
At unequal ranks its source is empty and its equation ideal is the unit
ideal. Thus off-diagonal stages retain a genuine obstruction unless the
whole coefficient stage is empty; they cannot be discarded by reduction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (J : A.IdealSheafData)
local instance doubleComparisonOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance doubleComparisonOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance doubleComparisonOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
variable (e : CategoryTheory.EquivalenceRelation p q) (hJ : J.comap p = J.comap q)
  (n m r s : ℕ)
local notation "c" => originalBoundaryComparison p q J hJ
local notation "l" => doubleRankMap (Over.mk p) x y n m r s

include e in
/-- The actual full original comparison has no source points at unequal endpoint ranks. -/
theorem originalBoundary_doubleRank_comparison_empty (hnm : n ≠ m) :
    IsEmpty (pullback c l : Scheme) := by
  refine ⟨fun z ↦ ?_⟩
  have hz : l (pullback.snd c l z) ∈ Set.range c := by
    refine ⟨pullback.fst c l z, ?_⟩
    exact congrArg (fun a : pullback c l ⟶ pullback f f ↦ a z) pullback.condition
  exact originalBoundary_comparison_not_rankCollision J e hJ _ hz
    ⟨n, m, hnm, doubleRankMap_endpoints (Over.mk p) x y n m r s _⟩

include e in
/-- The off-diagonal equation ideal is exactly the unit ideal, including all nilpotents. -/
theorem originalBoundary_doubleRank_comparison_ker_top (hnm : n ≠ m) :
    (pullback.snd c l).ker = ⊤ := by
  let _ := originalBoundary_doubleRank_comparison_empty J e hJ n m r s hnm
  exact Scheme.ker_eq_top_of_isEmpty _

variable [IsAffine A] [LocallyQuasiFinite p]

/-- Both source restrictions are finite, so the unchanged comparison is finite as well. -/
theorem originalBoundary_doubleRank_comparison_finite : IsFinite (pullback.snd c l) := by
  let _ := (originalBoundary_doubleRank_sources_finite (p := p) (q := q) J n m r s).1
  exact originalBoundary_comparison_test_finite J hJ l

include e in
/-- Every independent-rank stage has an actual closed comparison, without assuming coverage. -/
theorem originalBoundary_doubleRank_comparison_closedImmersion :
    IsClosedImmersion (pullback.snd c l) := by
  let _ := (originalBoundary_doubleRank_sources_finite (p := p) (q := q) J n m r s).1
  exact originalBoundary_comparison_test_closedImmersion J hJ l e

end FLT.Mazur.EquivalenceRelationOrderedFrames
