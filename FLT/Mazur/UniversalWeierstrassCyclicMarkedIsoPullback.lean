/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicFamilyRelationNaturality

/-!
# Pullback of a specified original full marked family isomorphism

The construction retains the specified comparison itself, as well as all labels.
Conjugation by the actual source comparisons detects equality of pulled-back maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Fixed isomorphisms on either side do not identify distinct comparisons. -/
theorem familyIso_conjugate_injective {C : Type*} [Category C] {A B D E : C}
    (a : A ≅ B) (b : D ≅ E) (d e : A ≅ D)
    (h : a.symm ≪≫ d ≪≫ b = a.symm ≪≫ e ≪≫ b) : d = e := by
  apply Iso.ext
  apply (cancel_epi a.inv).mp
  apply (cancel_mono b.hom).mp
  exact (Category.assoc _ _ _).trans ((congrArg Iso.hom h).trans
    (Category.assoc _ _ _).symm)

attribute [local irreducible] auxiliarySchemeGroup cyclicSchemeOriginalMarking
variable (n : ℕ) [NeZero n] {T U : Scheme}
  (f g : T ⟶ (cyclicAuxiliaryScheme n).left)
  (e : auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f) ≅
    auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n g)) (k : U ⟶ T)

/-- The specified original group comparison pulled back to the actual new source families. -/
irreducible_def cyclicMarkedFamilyIsoPullback :
    auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n (k ≫ f)) ≅
      auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n (k ≫ g)) :=
  (cyclicSourceOriginalGroupIso n f k).symm ≪≫
    (Over.pullback k).mapCommGrp.mapIso e ≪≫ cyclicSourceOriginalGroupIso n g k

/-- Pullback of the specified marked comparison preserves every original new-source label. -/
theorem cyclicMarkedFamilyIsoPullback_marking
    (hm : ∀ c : CyclicLabels n, cyclicSchemeOriginalMarking n f c ≫ e.hom.hom.hom.hom =
      cyclicSchemeOriginalMarking n g c) (c : CyclicLabels n) :
    cyclicSchemeOriginalMarking n (k ≫ f) c ≫
      (cyclicMarkedFamilyIsoPullback n f g e k).hom.hom.hom.hom =
        cyclicSchemeOriginalMarking n (k ≫ g) c :=
  auxiliarySchemeSection_iso_congr (cyclicSchemeOriginalMarking n (k ≫ f) c)
    (cyclicSchemeOriginalMarking n (k ≫ g) c) (cyclicMarkedFamilyIsoPullback n f g e k) _
    (cyclicMarkedFamilyIsoPullback_def n f g e k)
    (auxiliarySchemeSection_conjugate
      (cyclicSourceOriginalGroupIso n f k) ((Over.pullback k).mapCommGrp.mapIso e)
      (cyclicSourceOriginalGroupIso n g k) (cyclicSchemeOriginalMarking n (k ≫ f) c)
      (OverPullbackSection.lift k (auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f)).X
        (cyclicSourceOriginalSection n f k c))
      (OverPullbackSection.lift k (auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n g)).X
        (cyclicSourceOriginalSection n g k c)) (cyclicSchemeOriginalMarking n (k ≫ g) c)
      (cyclicSourceOriginalGroupIso_marking n f k c)
      (cyclicSourceOriginalSection_lift_compare n f g e hm k c)
      (cyclicSourceOriginalGroupIso_marking n g k c))

end FLT.Mazur.UniversalWeierstrass
