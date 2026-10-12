/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicNormalizationRelation

/-!
# Equal full normalizations compare the original marked group families

The comparison is built from the original normalization isomorphisms. It
retains every full label, including the cyclic factor outside the auxiliary frame.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Equality transport between equal frames is detected by the actual universal projection. -/
theorem auxiliarySchemeSection_transport {T : Scheme} (a b : T ⟶ levelFour.left) (h : a = b)
    (s : 𝟙_ (Over T) ⟶ (auxiliarySchemeGroup a).X)
    (t : 𝟙_ (Over T) ⟶ (auxiliarySchemeGroup b).X)
    (hs : s.left ≫ pullback.fst universalGroup.hom (a ≫ levelFour.hom) =
      t.left ≫ pullback.fst universalGroup.hom (b ≫ levelFour.hom)) :
    s ≫ (eqToIso (congrArg auxiliarySchemeGroup h)).hom.hom.hom.hom = t := by
  subst b
  change s ≫ 𝟙 _ = t
  rw [Category.comp_id]
  apply Over.OverMorphism.ext
  exact pullback.hom_ext hs (s.w.trans t.w.symm)

/-- Forgetting a three-part group comparison preserves its exact composition formula. -/
theorem auxiliarySchemeGroupIso_composite_hom {T : Scheme}
    {A B C D : CommGrp (Over T)} (e : A ≅ B) (d : A ≅ C) (k : C ≅ D) :
    (e.symm ≪≫ d ≪≫ k).hom.hom.hom.hom =
      e.inv.hom.hom.hom ≫ d.hom.hom.hom.hom ≫ k.hom.hom.hom.hom := rfl

/-- Three section equations compose without unfolding any geometric group structure. -/
theorem auxiliarySchemeSection_composite {T : Scheme} {A B C D E : Over T}
    (s : A ⟶ B) (a : B ⟶ C) (b : C ⟶ D) (c : D ⟶ E)
    (t : A ⟶ C) (u : A ⟶ D) (v : A ⟶ E)
    (hs : s ≫ a = t) (ht : t ≫ b = u) (hv : u ≫ c = v) :
    s ≫ (a ≫ b ≫ c) = v := by
  rw [← Category.assoc, ← Category.assoc, hs, ht, hv]

attribute [local irreducible] auxiliarySchemeGroup cyclicSchemeOriginalMarking
  cyclicSchemeNormalizedMarking

variable (n : ℕ) [NeZero n] {T : Scheme}
  (f g : T ⟶ (cyclicAuxiliaryScheme n).left)
  (h : cyclicSchemeNormalizedPoint n f = cyclicSchemeNormalizedPoint n g)

include h in
/-- The complete normalized equality retains the exact normalized auxiliary parameter. -/
theorem cyclicRelation_normalizedAuxiliary_eq :
    auxiliarySchemeNormalizedPoint (cyclicSchemeAuxiliaryPoint n f) =
      auxiliarySchemeNormalizedPoint (cyclicSchemeAuxiliaryPoint n g) := by
  rw [← cyclicSchemeNormalizedPoint_forget, ← cyclicSchemeNormalizedPoint_forget, h]

/-- The normalized family equality, sealed before composing actual group comparisons. -/
irreducible_def cyclicRelationNormalizedGroupIso :
    auxiliarySchemeGroup (auxiliarySchemeNormalizedPoint (cyclicSchemeAuxiliaryPoint n f)) ≅
      auxiliarySchemeGroup (auxiliarySchemeNormalizedPoint (cyclicSchemeAuxiliaryPoint n g)) :=
  eqToIso (congrArg auxiliarySchemeGroup (cyclicRelation_normalizedAuxiliary_eq n f g h))

/-- Equality of complete normalized parameters identifies every actual normalized section. -/
theorem cyclicRelation_normalizedMarking_transport (c : CyclicLabels n) :
    cyclicSchemeNormalizedMarking n f c ≫
      (eqToIso (congrArg auxiliarySchemeGroup
        (cyclicRelation_normalizedAuxiliary_eq n f g h))).hom.hom.hom.hom =
      cyclicSchemeNormalizedMarking n g c := by
  refine auxiliarySchemeSection_transport _ _
    (cyclicRelation_normalizedAuxiliary_eq n f g h) _ _ ?_
  rw [cyclicSchemeNormalizedMarking_fst, cyclicSchemeNormalizedMarking_fst, h]

/-- The actual group isomorphism comparing the two original full families in the relation. -/
irreducible_def cyclicRelationFamilyIso :
    auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f) ≅
      auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n g) :=
  (auxiliarySchemeNormalizationGroupIso (cyclicSchemeAuxiliaryPoint n f)).symm ≪≫
    cyclicRelationNormalizedGroupIso n f g h ≪≫
        auxiliarySchemeNormalizationGroupIso (cyclicSchemeAuxiliaryPoint n g)

/-- The actual comparison projects to the original three over-category comparisons. -/
theorem cyclicRelationFamilyIso_hom :
    (cyclicRelationFamilyIso n f g h).hom.hom.hom.hom =
      (auxiliarySchemeNormalizationGroupIso (cyclicSchemeAuxiliaryPoint n f)).inv.hom.hom.hom ≫
        (cyclicRelationNormalizedGroupIso n f g h).hom.hom.hom.hom ≫
            (auxiliarySchemeNormalizationGroupIso
              (cyclicSchemeAuxiliaryPoint n g)).hom.hom.hom.hom := by
  rw [cyclicRelationFamilyIso_def n f g h]
  exact auxiliarySchemeGroupIso_composite_hom
    (auxiliarySchemeNormalizationGroupIso (cyclicSchemeAuxiliaryPoint n f))
    (cyclicRelationNormalizedGroupIso n f g h)
    (auxiliarySchemeNormalizationGroupIso (cyclicSchemeAuxiliaryPoint n g))

/-- The family comparison lies over the unchanged original source scheme. -/
@[reassoc] theorem cyclicRelationFamilyIso_base :
    (cyclicRelationFamilyIso n f g h).hom.hom.hom.hom.left ≫
      (auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n g)).X.hom =
        (auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f)).X.hom :=
  (cyclicRelationFamilyIso n f g h).hom.hom.hom.hom.w

end FLT.Mazur.UniversalWeierstrass
