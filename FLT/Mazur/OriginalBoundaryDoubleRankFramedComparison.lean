/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryRankFrameCover
public import FLT.Mazur.RelativeDoubleRankThickenings

/-!
# Constructed full comparisons on every independent rank stage

At every independent pair of ranks and infinitesimal orders, an actual etale
frame cover splits the original comparison into full coordinate equations.
Coverage of these equations remains an obligation; rank equality is not assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "P" => pullback.snd p J.subschemeι
local notation "Q" => InvariantIdealRelation.snd J p q hJ
local notation "E" => Over.mk P
local notation "c" => originalBoundaryComparison p q J hJ
local instance doubleFrameBoundaryOver_separated : IsSeparated (E).hom :=
  inferInstanceAs (IsSeparated P)
local instance doubleFrameBoundaryOver_etale : Etale (E).hom := inferInstanceAs (Etale P)
local instance doubleFrameBoundaryOver_compact : QuasiCompact (E).hom :=
  inferInstanceAs (QuasiCompact P)
local instance doubleFrameOriginalOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance doubleFrameOriginalOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance doubleFrameOriginalOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n m r s : ℕ)
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "t" => doubleRankMap (Over.mk p) x y n m r s
local notation "v" => originalBoundaryRankFrameProjection J t n
local notation "a" => originalBoundaryRankCoverFrame J t n
attribute [local irreducible] doubleRankMap doubleRankThickening

omit [QuasiCompact p] in
/-- Every full independent-rank chart has the original first rank needed for framing. -/
theorem originalBoundary_doubleRank_frame_rank :
    Set.range (t ≫ pullback.fst f f ≫ J.subschemeι) ⊆ exactRank (Over.mk p) n := by
  rintro _ ⟨z, rfl⟩
  exact (doubleRankMap_endpoints (Over.mk p) x y n m r s z).1

/-- The actual original frame cover is surjective at every pair of ranks and orders. -/
theorem originalBoundary_doubleRank_frame_surjective : Function.Surjective v :=
  originalBoundaryRankFrameProjection_surjective J t n
    (originalBoundary_doubleRank_frame_rank J n m r s)

/-- Every full independent-rank comparison splits on the constructed etale frame cover. -/
def originalBoundaryDoubleRankFrameComparisonIso :
    (∐ fun i : Fin n ↦ frameEquationChart E (Fin n) a Q
      ((v ≫ t) ≫ pullback.snd f f) i) ≅ pullback c (v ≫ t) :=
  originalBoundaryRankFrameComparisonIso J hJ t n
    (originalBoundary_doubleRank_frame_rank J n m r s)

/-- Covering framed tests is equivalent to covering the whole original independent-rank test. -/
theorem originalBoundary_doubleRank_coverage_iff_framed :
    Set.range t ⊆ Set.range c ↔ Set.range (v ≫ t) ⊆ Set.range c := by
  have hr : Set.range (v ≫ t) = Set.range t :=
    (originalBoundary_doubleRank_frame_surjective J n m r s).range_comp t
  rw [hr]

end FLT.Mazur.EquivalenceRelationOrderedFrames
