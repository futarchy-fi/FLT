/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryRankOnePairs
public import FLT.Mazur.OriginalBoundaryComparisonClosedImage
public import FLT.Mazur.RelativeDoubleRankThickenings

/-!
# Full original comparison on rank-one coefficient tests

The rank-one comparison is detected by exact equality of the two boundary
morphisms. Equal endpoints construct a unique original arrow. The criterion
applies in particular to every full independent-rank thickening with first
rank one, at every pair of orders.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (J : A.IdealSheafData)
  (e : CategoryTheory.EquivalenceRelation p q) (hJ : J.comap p = J.comap q)
local instance oneComparisonOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance oneComparisonOver_etale : Etale (Over.mk p).hom := ‹Etale p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
attribute [local irreducible] doubleRankMap doubleRankThickening
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "c" => originalBoundaryComparison p q J hJ

include e in
/-- Exact endpoint equality characterizes the full original rank-one comparison. -/
theorem originalBoundary_rankOne_comparison_lift_iff (t : B ⟶ pullback f f)
    (ht : Set.range (t ≫ x) ⊆ rankAtMost (Over.mk p) 1) :
    (∃! d : B ⟶ pullback p J.subschemeι, d ≫ c = t) ↔
      t ≫ pullback.fst f f = t ≫ pullback.snd f f := by
  let _ := originalBoundaryComparison_mono e J hJ
  have ht' : Set.range ((t ≫ pullback.fst f f) ≫ J.subschemeι) ⊆
      rankAtMost (Over.mk p) 1 := by
    simpa only [Category.assoc] using ht
  constructor
  · intro h
    let d := h.choose
    have hd := h.choose_spec.1
    apply originalBoundary_rankOne_endpoints_eq e J hJ _ _ ht' d
    · simpa only [originalBoundaryComparison, Category.assoc, pullback.lift_fst] using
        congrArg (fun a ↦ a ≫ pullback.fst f f) hd
    · simpa only [originalBoundaryComparison, Category.assoc, pullback.lift_snd] using
        congrArg (fun a ↦ a ≫ pullback.snd f f) hd
  · intro h
    let hd := (originalBoundary_rankOne_arrow_iff e J hJ _ _ ht').mpr h
    let d := hd.choose
    have he : d ≫ c = t := by
      apply pullback.hom_ext
      · simpa only [originalBoundaryComparison, Category.assoc, pullback.lift_fst] using
          hd.choose_spec.1.1
      · simpa only [originalBoundaryComparison, Category.assoc, pullback.lift_snd] using
          hd.choose_spec.1.2
    exact ⟨d, he, fun d' hd' ↦ (cancel_mono c).mp (hd'.trans he.symm)⟩

include e in
/-- Every independent second rank and both full infinitesimal orders retain this criterion. -/
theorem originalBoundary_doubleRank_one_lift_iff (m r s : ℕ) :
    (∃! d : doubleRankThickening (Over.mk p) x y 1 m r s ⟶
        pullback p J.subschemeι,
      d ≫ c = doubleRankMap (Over.mk p) x y 1 m r s) ↔
      doubleRankMap (Over.mk p) x y 1 m r s ≫ pullback.fst f f =
        doubleRankMap (Over.mk p) x y 1 m r s ≫ pullback.snd f f := by
  apply originalBoundary_rankOne_comparison_lift_iff J e hJ
  rintro _ ⟨z, rfl⟩
  exact (doubleRankMap_endpoints (Over.mk p) x y 1 m r s z).1.2

end FLT.Mazur.EquivalenceRelationOrderedFrames
