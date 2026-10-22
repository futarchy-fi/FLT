/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryDoubleRankArrowCriterion
public import FLT.Mazur.RelativeDoubleRankGlobalLifts

/-!
# Original boundary arrows on whole locally Noetherian coefficient schemes

Closed comparison detection and affine gluing construct an original arrow
on a possibly nonaffine, noncompact coefficient test. Full first-source
finiteness supplies closedness. Both original endpoint equations hold on
the entire test; all-order arrows are still the explicit geometric input.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A}
  [IsAffine A] [IsNoetherian A] [IsSeparated p] [Etale p] [QuasiCompact p]
  [IsLocallyNoetherian B]
  (J : A.IdealSheafData) (e : CategoryTheory.EquivalenceRelation p q)
  (hJ : J.comap p = J.comap q)
local instance globalDoubleOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance globalDoubleOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance globalDoubleOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "c" => originalBoundaryComparison p q J hJ
include e

/-- All independent rank orders construct a unique arrow on the full coefficient scheme. -/
theorem originalBoundary_global_unique_lift_of_doubleRank
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : ∀ n m r s : ℕ,
      ∃ d : doubleRankThickening (Over.mk p) (t ≫ x) (t ≫ y) n m r s ⟶
        pullback p J.subschemeι,
      d ≫ c = doubleRankMap (Over.mk p) (t ≫ x) (t ≫ y) n m r s ≫ t) :
    ∃! d : B ⟶ pullback p J.subschemeι, d ≫ c = t := by
  let _ := originalBoundaryComparison_mono e J hJ
  let _ := originalBoundary_comparison_test_closedImmersion J hJ t e
  exact existsUnique_global_lift_of_doubleRank (Over.mk p) (t ≫ x) (t ≫ y) c t h

/-- The constructed whole-scheme arrow solves both unchanged original endpoint equations. -/
theorem originalBoundary_global_endpoints_of_doubleRank
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : ∀ n m r s : ℕ,
      ∃ d : doubleRankThickening (Over.mk p) (t ≫ x) (t ≫ y) n m r s ⟶
        pullback p J.subschemeι,
      d ≫ c = doubleRankMap (Over.mk p) (t ≫ x) (t ≫ y) n m r s ≫ t) :
    ∃! d : B ⟶ pullback p J.subschemeι,
      d ≫ pullback.snd p J.subschemeι = t ≫ pullback.fst f f ∧
      d ≫ InvariantIdealRelation.snd J p q hJ = t ≫ pullback.snd f f := by
  obtain ⟨d, hd, huniq⟩ := originalBoundary_global_unique_lift_of_doubleRank J e hJ t h
  have hfirst := congrArg (fun a ↦ a ≫ pullback.fst f f) hd
  have hsecond := congrArg (fun a ↦ a ≫ pullback.snd f f) hd
  simp only [Category.assoc, originalBoundaryComparison, pullback.lift_fst,
    pullback.lift_snd] at hfirst hsecond
  refine ⟨d, ⟨hfirst, hsecond⟩, ?_⟩
  intro d' hd'
  apply huniq d'
  apply pullback.hom_ext
  · simpa only [Category.assoc, originalBoundaryComparison, pullback.lift_fst] using hd'.1
  · simpa only [Category.assoc, originalBoundaryComparison, pullback.lift_snd] using hd'.2

end FLT.Mazur.EquivalenceRelationOrderedFrames
