/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryFramedEquations
public import FLT.Mazur.RelativeExactRankFrameCover

/-!
# Constructed frame covers for full original boundary comparisons

Every coefficient test with a fixed original first rank admits a constructed
etale surjection carrying a complete frame. On that cover the entire original
comparison is the disjoint union of full coordinate endpoint equations.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "P" => pullback.snd p J.subschemeι
local notation "Q" => InvariantIdealRelation.snd J p q hJ
local notation "E" => Over.mk P
local notation "c" => originalBoundaryComparison p q J hJ
local instance rankCoverBoundaryOver_separated : IsSeparated (E).hom :=
  inferInstanceAs (IsSeparated P)
local instance rankCoverBoundaryOver_etale : Etale (E).hom := inferInstanceAs (Etale P)
local instance rankCoverBoundaryOver_compact : QuasiCompact (E).hom :=
  inferInstanceAs (QuasiCompact P)
local instance rankCoverOriginalOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance rankCoverOriginalOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance rankCoverOriginalOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (t : B ⟶ pullback
    (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))
    (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤))))
  (n : ℕ)
local notation "x" => t ≫ pullback.fst f f
local notation "y" => t ≫ pullback.snd f f
/-- The original boundary frame scheme supplies the full coefficient cover. -/
abbrev originalBoundaryRankFrameCover := rankFrameCover E n x

/-- The constructed cover retains the original scalar coefficient test. -/
abbrev originalBoundaryRankFrameProjection : originalBoundaryRankFrameCover J t n ⟶ B :=
  rankFrameProjection E n x

/-- The actual frame-cover map is etale, without reducing the coefficient scheme. -/
instance originalBoundaryRankFrameProjection_etale :
    Etale (originalBoundaryRankFrameProjection J t n) := inferInstance

/-- The tautological boundary frame over the unchanged scalar pair on the cover. -/
def originalBoundaryRankCoverFrame :
    Over.mk ((originalBoundaryRankFrameProjection J t n ≫ t) ≫ pullback.fst f f) ⟶
      distinctScheme E (Fin n) :=
  Over.homMk (rankCoverFrame E n x).left (by
    change _ ≫ _ = (originalBoundaryRankFrameProjection J t n ≫ t) ≫ pullback.fst f f
    rw [Category.assoc]
    exact (rankCoverFrame E n x).w)

variable (ht : Set.range (t ≫ pullback.fst _ _ ≫ J.subschemeι) ⊆ exactRank (Over.mk p) n)
include ht

/-- Original exact rank constructs a surjective cover by full boundary frames. -/
theorem originalBoundaryRankFrameProjection_surjective :
    Function.Surjective (originalBoundaryRankFrameProjection J t n) := by
  apply rankFrameProjection_surjective E n x
  rintro _ ⟨z, rfl⟩
  exact (exactRank_pullback_iff (Over.mk p) J.subschemeι (x z) n).mpr (ht ⟨z, rfl⟩)

omit [QuasiCompact p] in
/-- The full cover still has the same original first-endpoint rank. -/
theorem originalBoundaryRankFrameTest_rank :
    Set.range ((originalBoundaryRankFrameProjection J t n ≫ t) ≫
      pullback.fst f f ≫ J.subschemeι) ⊆ exactRank (Over.mk p) n := by
  rintro _ ⟨z, rfl⟩
  exact ht ⟨originalBoundaryRankFrameProjection J t n z, rfl⟩

/-- After a constructed etale surjection, every full comparison splits into actual equations. -/
def originalBoundaryRankFrameComparisonIso :
    (∐ fun i : Fin n ↦ frameEquationChart E (Fin n)
      (originalBoundaryRankCoverFrame J t n) Q
      ((originalBoundaryRankFrameProjection J t n ≫ t) ≫ pullback.snd f f) i) ≅
        pullback c (originalBoundaryRankFrameProjection J t n ≫ t) :=
  originalBoundaryFramedComparisonIso J hJ (originalBoundaryRankFrameProjection J t n ≫ t)
    n (originalBoundaryRankCoverFrame J t n) (originalBoundaryRankFrameTest_rank J t n ht)

end FLT.Mazur.EquivalenceRelationOrderedFrames
