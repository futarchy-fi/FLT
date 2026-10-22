/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonOriginalGroup
public import FLT.Mazur.GeneralizedCurvePointTranslation
public import FLT.Mazur.PolygonGeneralizedCurveActionExt
public import FLT.Mazur.PolygonSplitIdentityGroup

/-!
# The original action on an abstract one-gon

Translate the given whole curve to align its identity with the pinching model.
Torus rigidity identifies the original group laws, and density extends their
comparison to the whole original action, including the node.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open CartesianMonoidalCategory
namespace FLT.Mazur.OneGonOriginalAction
open PolygonPinching OneGonOriginalGroup GroupObjectPointTranslation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K]
  (E : GeneralizedEllipticCurve (Spec (.of K)))
  (p : components K 1 ⟶ E.curve) (q : nodes K 1 ⟶ E.curve)
  (h : IsPushout (toComponents K 1 Nat.zero_lt_one) (toNodes K 1) p q)
local notation "F" => PolygonGeneralizedCurve.curve K 1 Nat.zero_lt_one p q h
local notation "T" => MultiplicativeGroupScheme.gm K

/-- The single torus inclusion retains the canonical split group law. -/
theorem splitTorusIso_hom : (splitTorusIso (K := K)).hom =
    PolygonSplitGroup.component K 1 0 := by
  apply (cancel_mono (splitTorusIso (K := K)).inv).mp
  simp [splitTorusIso, PolygonSplitGroup.component]

instance splitTorusIso_isMonHom : IsMonHom (splitTorusIso (K := K)).hom := by
  rw [splitTorusIso_hom]
  infer_instance

/-- Both original groups present the very same smooth open of the same curve. -/
def smoothComparison : (F).group ≅ E.group := (F).smoothIso ≪≫ E.smoothIso.symm

/-- The comparison before pointing already preserves the full smooth inclusion. -/
theorem smoothComparison_inclusion :
    (smoothComparison E p q h).hom ≫ E.inclusion = (F).inclusion := by
  simp only [smoothComparison, GeneralizedEllipticCurve.inclusion, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- The correction is the inverse of the old model identity in the given original group. -/
def correction : 𝟙_ (Over (Spec (.of K))) ⟶ E.group :=
  (η[(F).group] ≫ (smoothComparison E p q h).hom)⁻¹

/-- Normalize the group comparison using its original, independently specified law. -/
def groupComparison : (F).group ≅ E.group :=
  smoothComparison E p q h ≪≫ translationIso (correction E p q h)

/-- The corrected comparison carries the model identity to the actual original identity. -/
theorem groupComparison_one :
    η[(F).group] ≫ (groupComparison E p q h).hom = η[E.group] := by
  change η[(F).group] ≫ (smoothComparison E p q h).hom ≫
    translation (correction E p q h) = _
  rw [← Category.assoc, comp_translation]
  simp only [correction, toUnit_unit, Category.id_comp, inv_mul_cancel, MonObj.one_eq_one]

/-- Rigidity proves that this comparison preserves the pre-existing original multiplication. -/
instance groupComparison_isMonHom : IsMonHom (groupComparison E p q h).hom := by
  let e := splitTorusIso ≪≫ groupComparison E p q h
  have he : η[(T)] ≫ e.hom = η[E.group] := by
    change η[(T)] ≫ (splitTorusIso (K := K)).hom ≫ _ = _
    rw [← Category.assoc, IsMonHom.one_hom, groupComparison_one]
  let _ := TorusGroupLawRigidity.isMonHom_of_pointedIso e he
  have hd : (groupComparison E p q h).hom =
      (splitTorusIso (K := K)).inv ≫ e.hom := by simp [e]
  rw [hd]
  infer_instance

/-- Translation aligns the entire original curve with the corrected smooth comparison. -/
theorem translated_inclusion :
    (F).inclusion ≫ (E.pointTranslationIso (correction E p q h)).hom =
      (groupComparison E p q h).hom ≫ E.inclusion := by
  rw [← smoothComparison_inclusion E p q h, Category.assoc,
    E.inclusion_pointTranslation]
  rfl

/-- Every original abstract one-gon has the canonical full generalized-curve structure up to iso. -/
def originalIso : (F) ≅ E :=
  PolygonGeneralizedCurve.isoOfInclusion K 1 Nat.zero_lt_one p q h
    (E.pointTranslationIso (correction E p q h))
    (groupComparison E p q h) (translated_inclusion E p q h)

end FLT.Mazur.OneGonOriginalAction
