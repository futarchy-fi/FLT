/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryDoubleRankComparison
public import FLT.Mazur.RelativeDoubleRankComparisonTransitions

/-!
# Exact original comparison ideals across independent orders

The unchanged original boundary comparison has cartesian order transitions.
Its entire equation ideal, including nilpotent equations, pulls back exactly
from higher orders. The maps relate orders at fixed ranks; they do not supply
comparison coverage or an original arrow between unrelated endpoints.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
local instance orderIdealOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance orderIdealOver_etale : Etale (Over.mk p).hom := ‹Etale p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
attribute [local irreducible] doubleRankMap doubleRankThickening
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "c" => originalBoundaryComparison p q J hJ
variable (n m : ℕ)

/-- The exact original boundary comparisons form cartesian squares at fixed independent ranks. -/
theorem originalBoundary_rankComparison_order_square {r s r' s' : ℕ}
    (hr : r ≤ r') (hs : s ≤ s') :
    IsPullback (pullback.snd c (doubleRankMap (Over.mk p) x y n m r s))
      (doubleRankComparisonTransition (Over.mk p) x y n m c hr hs)
      (doubleRankTransition (Over.mk p) x y n m hr hs)
      (pullback.snd c (doubleRankMap (Over.mk p) x y n m r' s')) :=
  doubleRankComparisonTransition_isPullback (Over.mk p) x y n m c hr hs

variable [QuasiCompact p] [IsAffine A] [LocallyQuasiFinite p]
  (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- All original comparison equations restrict exactly at both independent thickening orders. -/
theorem originalBoundary_rankComparison_order_kernel {r s r' s' : ℕ}
    (hr : r ≤ r') (hs : s ≤ s') :
    (pullback.snd c (doubleRankMap (Over.mk p) x y n m r' s')).ker.comap
      (doubleRankTransition (Over.mk p) x y n m hr hs) =
        (pullback.snd c (doubleRankMap (Over.mk p) x y n m r s)).ker := by
  let _ := originalBoundary_doubleRank_comparison_closedImmersion J e hJ n m r' s'
  exact doubleRankComparisonTransition_kernel (Over.mk p) x y n m c hr hs

end FLT.Mazur.EquivalenceRelationOrderedFrames
