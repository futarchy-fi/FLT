/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNormalizationComplex
public import FLT.Mazur.ModuleExactOpenCover
/-!
# Transport of the normalization sequence

A cocone isomorphism preserves the actual structure inclusion and branch
difference. Restriction along its inverse reflects short exactness.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.Modules
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.PolygonNormalizationTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open PolygonPinching PolygonStructureInclusion PolygonBranchDifferenceSheaf
open PolygonNormalizationComplex StructureDirectImage
variable (K : Type u) [Field K] (n : ℕ) (hn : 0 < n)
  {C D : Over (Spec (.of K))}
  (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (p' : components K n ⟶ D) (q' : nodes K n ⟶ D)
  (h' : IsPushout (toComponents K n hn) (toNodes K n) p' q')
  (e : D ≅ C) (hp : p' ≫ e.hom = p) (hq : q' ≫ e.hom = q)

private instance left_iso : IsIso e.hom.left :=
  inferInstanceAs (IsIso ((Over.forget _).map e.hom))
include hp in
theorem normalization_square : IsPullback p'.left (𝟙 _) e.hom.left p.left := by
  apply IsPullback.flip
  apply IsPullback.of_horiz_isIso_mono
  refine ⟨?_⟩
  simpa only [Category.id_comp, Over.comp_left] using (congrArg Over.Hom.left hp).symm
include hq in
theorem node_square : IsPullback q'.left (𝟙 _) e.hom.left q.left := by
  apply IsPullback.flip
  apply IsPullback.of_horiz_isIso_mono
  refine ⟨?_⟩
  simpa only [Category.id_comp, Over.comp_left] using (congrArg Over.Hom.left hq).symm

/-- A cocone isomorphism identifies the actual normalization complexes. -/
def iso : (complex K n hn p q h).map (restrictFunctor e.hom.left) ≅
    complex K n hn p' q' h' := by
  let : (restrictFunctor e.hom.left).Additive := { map_add := rfl }
  let hN := normalization_square K n p p' e hp
  let hD := node_square K n q q' e hq
  refine ShortComplex.isoMk (restrictUnitIso e.hom.left)
    (StructureImageOpenChart.iso p.left p'.left (𝟙 _) e.hom.left hN)
    (StructureImageOpenChart.iso q.left q'.left (𝟙 _) e.hom.left hD) ?_ ?_
  · exact (StructureImageOpenChart.unit_iso p.left p'.left (𝟙 _) e.hom.left hN).symm
  · change _ ≫ (branchRestriction K n hn p' q' h' false -
      branchRestriction K n hn p' q' h' true) =
      (restrictFunctor e.hom.left).map (branchRestriction K n hn p q h false -
        branchRestriction K n hn p q h true) ≫ _
    rw [Functor.map_sub, Preadditive.comp_sub, Preadditive.sub_comp]
    congr 1
    all_goals
      apply Eq.symm
      apply StructureImageOpenChart.restriction_iso
      simp

include hp hq in
theorem shortExact (hs : (complex K n hn p' q' h').ShortExact) :
    (complex K n hn p q h).ShortExact := by
  let E : D.left ≅ C.left := (Over.forget _).mapIso e
  let : (𝟭 C.left.Modules).Additive := { map_add := rfl }
  have ht : ((complex K n hn p q h).map (restrictFunctor e.hom.left)).ShortExact :=
    ShortComplex.shortExact_of_iso (iso K n hn p q h p' q' h' e hp hq).symm hs
  let α := (restrictFunctorComp E.inv E.hom).symm ≪≫
    restrictFunctorCongr E.inv_hom_id ≪≫ restrictFunctorId
  exact ShortComplex.shortExact_of_iso ((complex K n hn p q h).mapNatIso α)
    (ht.map_of_exact (restrictFunctor E.inv))
end FLT.Mazur.PolygonNormalizationTransport
