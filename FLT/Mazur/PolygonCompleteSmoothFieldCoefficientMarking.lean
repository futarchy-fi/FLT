/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothFieldCoefficientCurve
public import FLT.Mazur.GroupSectionBaseChange

/-!
# Exact original markings under full field coefficient comparison

The projection formula determines the entire pulled-back section, so every
original label, including the chosen identity, is preserved before projection.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
  (M : Type) [Field M] [Algebra L M]
  {Z : Scheme} (r : Z ⟶ exactVeroneseProj K n h) (s : Z ⟶ Spec (.of M))
  (ht : IsPullback r s (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom ((algebraMap L M).comp a))))
local notation "aM" => RingHom.comp (algebraMap L M) a
local notation "haM" => Iff.mpr (map_ne_zero (algebraMap L M)) ha
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap L M))
local notation "E" => completeFieldGeneralizedCurve K n h L a ha p q hs
local notation "D" => completeFieldGeneralizedCurve K n h M aM haM r s ht
local notation "u" => completeCartesianBaseMap K n h
  (Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom aM)) p q hs r s ht b
  (completeCoefficientSpec_comp K L a M)

local notation "e" => completeFieldCoefficientCurveIso K n h L a ha p q hs M r s ht

/-- The inverse DR comparison takes each original label to its actual pulled section. -/
theorem completeFieldCoefficientCurveIso_marking_inv (i j : Fin n) :
    completeFieldMarkedPoint K n h M aM r s ht j ≫ (e i).inv.curve =
      GroupSectionBaseChange.pullSection b (completeFieldMarkedPoint K n h L a p q hs j) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change completeCartesianMarking K n h _ r s ht j ≫
      (e i).inv.curve.left ≫ pullback.fst q b = _
    rw [completeFieldCoefficientCurveIso_marking]
    exact (GroupSectionBaseChange.section_fst b
      (completeFieldMarkedPoint K n h L a p q hs j)).symm
  · exact (completeFieldMarkedPoint K n h M aM r s ht j ≫ (e i).inv.curve).w.trans
      (GroupSectionBaseChange.pullSection b
        (completeFieldMarkedPoint K n h L a p q hs j)).w.symm

/-- The full DR comparison preserves every original label as an actual section. -/
theorem completeFieldCoefficientCurveIso_marking_hom (i j : Fin n) :
    GroupSectionBaseChange.pullSection b (completeFieldMarkedPoint K n h L a p q hs j) ≫
        (e i).hom.curve = completeFieldMarkedPoint K n h M aM r s ht j := by
  rw [← completeFieldCoefficientCurveIso_marking_inv K n h L a ha p q hs M r s ht i j]
  change (_ ≫ (e i).inv.curve) ≫ (e i).hom.curve = _
  have he := congrArg GeneralizedEllipticCurve.Hom.curve (e i).inv_hom_id
  change (e i).inv.curve ≫ (e i).hom.curve = 𝟙 _ at he
  rw [Category.assoc, he, Category.comp_id]

end FLT.Mazur.PolygonInfinitesimalStages
