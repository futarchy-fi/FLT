/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBranchSequence
public import FLT.Mazur.StructureImageOpenChart

/-!
# Comparing the polygon normalization complex on affine charts

The source complex uses the existing structure inclusion and branch difference.
Cartesian normalization and node squares, together with the two endpoint
equations, identify its restriction with the computed affine complex.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.Modules
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.PolygonNormalizationComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open PolygonPinching PolygonStructureInclusion PolygonBranchDifferenceSheaf
open StructureDirectImage
variable (K : Type u) [Field K] (n : ℕ) (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
/-- The specified polygon structure, normalization and branch-difference complex. -/
def complex : ShortComplex C.left.Modules :=
  ShortComplex.mk (inclusion K n p) (difference K n hn p q h)
    (inclusion_difference K n hn p q h)
variable {R S T : CommRingCat.{u}} (f : R ⟶ S) (a b : S ⟶ T) (d : R ⟶ T)
  (wa : Spec.map a ≫ Spec.map f = Spec.map d)
  (wb : Spec.map b ≫ Spec.map f = Spec.map d)
  (j : Spec R ⟶ C.left) (iN : Spec S ⟶ (components K n).left)
  (iD : Spec T ⟶ (nodes K n).left)
  [IsOpenImmersion j] [IsOpenImmersion iN] [IsOpenImmersion iD]
  (hN : IsPullback (Spec.map f) iN j p.left)
  (hD : IsPullback (Spec.map d) iD j q.left)
  (ha : Spec.map a ≫ iN = iD ≫ (branchSection K n hn false).left)
  (hb : Spec.map b ≫ iN = iD ≫ (branchSection K n hn true).left)
/-- Geometric cartesian squares and endpoint equations identify the actual chart complex. -/
def chartIso : (complex K n hn p q h).map (restrictFunctor j) ≅
    AffineBranchSequence.complex f a b d wa wb := by
  let : (restrictFunctor j).Additive := { map_add := rfl }
  refine ShortComplex.isoMk (restrictUnitIso j)
    (StructureImageOpenChart.iso p.left (Spec.map f) iN j hN)
    (StructureImageOpenChart.iso q.left (Spec.map d) iD j hD) ?_ ?_
  · exact (StructureImageOpenChart.unit_iso p.left (Spec.map f) iN j hN).symm
  · change _ ≫ (AffineBranchSequence.branch f d a wa - AffineBranchSequence.branch f d b wb) =
      (restrictFunctor j).map (branchRestriction K n hn p q h false -
        branchRestriction K n hn p q h true) ≫ _
    rw [Functor.map_sub, Preadditive.comp_sub, Preadditive.sub_comp]
    congr 1
    · exact (StructureImageOpenChart.restriction_iso p.left (Spec.map f) iN j hN
        (branchSection K n hn false).left q.left
        (congrArg Over.Hom.left (branchSection_normalization K n hn p q h false))
        (Spec.map a) (Spec.map d) wa iD hD ha).symm
    · exact (StructureImageOpenChart.restriction_iso p.left (Spec.map f) iN j hN
        (branchSection K n hn true).left q.left
        (congrArg Over.Hom.left (branchSection_normalization K n hn p q h true))
        (Spec.map b) (Spec.map d) wb iD hD hb).symm
include wa wb hN hD ha hb in
theorem chart_shortExact (hi : Function.Injective f)
    (he : ∀ s : S, a s = b s → ∃ r : R, f r = s)
    (hs : Function.Surjective (fun s : S ↦ a s - b s)) :
    ((complex K n hn p q h).map (restrictFunctor j)).ShortExact :=
  ShortComplex.shortExact_of_iso
    (chartIso K n hn p q h f a b d wa wb j iN iD hN hD ha hb).symm
    (AffineBranchSequence.shortExact f a b d wa wb hi he hs)
end FLT.Mazur.PolygonNormalizationComplex
