/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicAffineFamilyRelation
public import FLT.Mazur.UniversalWeierstrassCyclicSourceMarking

/-!
# The genuine full marked family relation is stable under source change

Pulling back a marked group comparison and conjugating by the actual source
comparisons preserves every original full label.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] auxiliarySchemeGroup cyclicSchemeOriginalMarking
variable (n : ℕ) [NeZero n] {T U : Scheme}
  (f g : T ⟶ (cyclicAuxiliaryScheme n).left)
  (e : auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f) ≅
    auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n g))
  (hm : ∀ c : CyclicLabels n, cyclicSchemeOriginalMarking n f c ≫ e.hom.hom.hom.hom =
    cyclicSchemeOriginalMarking n g c) (k : U ⟶ T)

include hm in
/-- The original relative sections retain their comparison after changing the source. -/
theorem cyclicSourceOriginalSection_compare (c : CyclicLabels n) :
    cyclicSourceOriginalSection n f k c ≫ e.hom.hom.hom.hom =
      cyclicSourceOriginalSection n g k c := by
  apply Over.OverMorphism.ext
  change (k ≫ (cyclicSchemeOriginalMarking n f c).left) ≫ e.hom.hom.hom.hom.left =
    k ≫ (cyclicSchemeOriginalMarking n g c).left
  rw [Category.assoc, ← Over.comp_left, hm c]

include hm in
/-- Lifting the original sections commutes with the actual pulled-back group isomorphism. -/
theorem cyclicSourceOriginalSection_lift_compare (c : CyclicLabels n) :
    OverPullbackSection.lift k (auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f)).X
      (cyclicSourceOriginalSection n f k c) ≫
        ((Over.pullback k).mapCommGrp.mapIso e).hom.hom.hom.hom =
      OverPullbackSection.lift k (auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n g)).X
        (cyclicSourceOriginalSection n g k c) := by
  change _ ≫ (Over.pullback k).map e.hom.hom.hom.hom = _
  rw [OverPullbackSection.lift_map, cyclicSourceOriginalSection_compare n f g e hm k c]

/-- The genuine marked group-family relation pulls back along every source morphism. -/
theorem CyclicMarkedFamilyRelated.pullback (h : CyclicMarkedFamilyRelated n f g) :
    CyclicMarkedFamilyRelated n (k ≫ f) (k ≫ g) := by
  obtain ⟨d, hd⟩ := h
  refine ⟨(cyclicSourceOriginalGroupIso n f k).symm ≪≫
    (Over.pullback k).mapCommGrp.mapIso d ≪≫ cyclicSourceOriginalGroupIso n g k, ?_⟩
  intro c
  exact auxiliarySchemeSection_conjugate
    (cyclicSourceOriginalGroupIso n f k) ((Over.pullback k).mapCommGrp.mapIso d)
    (cyclicSourceOriginalGroupIso n g k)
    (cyclicSchemeOriginalMarking n (k ≫ f) c)
    (OverPullbackSection.lift k (auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f)).X
      (cyclicSourceOriginalSection n f k c))
    (OverPullbackSection.lift k (auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n g)).X
      (cyclicSourceOriginalSection n g k c))
    (cyclicSchemeOriginalMarking n (k ≫ g) c)
    (cyclicSourceOriginalGroupIso_marking n f k c)
    (cyclicSourceOriginalSection_lift_compare n f g d hd k c)
    (cyclicSourceOriginalGroupIso_marking n g k c)

end FLT.Mazur.UniversalWeierstrass
