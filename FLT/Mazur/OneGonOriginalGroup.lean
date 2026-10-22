/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TorusGroupLawRigidity
public import FLT.Mazur.PolygonGeneralizedCurve
public import FLT.Mazur.GroupObjectPointTranslation

/-!
# The pre-existing smooth group of an abstract one-gon

An arbitrary generalized curve whose whole curve is a one-gon has a torus
presentation of its original group law. The pinching supplies the unpointed
chart; translating by the inverse image of the actual identity points it.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonOriginalGroup
open PolygonPinching GroupObjectPointTranslation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K]
  (E : GeneralizedEllipticCurve (Spec (.of K)))
  (p : components K 1 ⟶ E.curve) (q : nodes K 1 ⟶ E.curve)
  (h : IsPushout (toComponents K 1 (by decide)) (toNodes K 1) p q)
local notation "T" => MultiplicativeGroupScheme.gm K

/-- The single canonical split component is the entire smooth group. -/
def splitTorusIso : (T) ≅ PolygonSplitGroup.model K 1 :=
  (coproductUniqueIso (fun _ : ZMod 1 ↦ (T))).symm

/-- Pinching identifies the actual smooth locus, before normalizing its identity. -/
def unpointedIso : (T) ≅ E.group :=
  splitTorusIso ≪≫ (smoothIso K 1 (by decide) p q h).symm ≪≫ E.smoothIso.symm

/-- The actual original identity expressed in the full torus chart. -/
def identityCoordinate : 𝟙_ (Over (Spec (.of K))) ⟶ (T) :=
  η[E.group] ≫ (unpointedIso E p q h).inv

/-- Translate the original pinching chart to the original group identity. -/
def pointedIso : (T) ≅ E.group :=
  translationIso (identityCoordinate E p q h) ≪≫ unpointedIso E p q h

/-- The constructed chart preserves the original identity as a morphism. -/
theorem pointedIso_one : η[(T)] ≫ (pointedIso E p q h).hom = η[E.group] := by
  change η[(T)] ≫ translation (identityCoordinate E p q h) ≫
    (unpointedIso E p q h).hom = _
  rw [← Category.assoc]
  have he : η[(T)] = (1 : 𝟙_ (Over (Spec (.of K))) ⟶ (T)) := MonObj.one_eq_one _
  rw [he, one_translation]
  simp only [identityCoordinate, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The torus chart identifies the given group law, without assuming compatibility. -/
instance pointedIso_isMonHom : IsMonHom (pointedIso E p q h).hom :=
  TorusGroupLawRigidity.isMonHom_of_pointedIso _ (pointedIso_one E p q h)

/-- An original abstract one-gon's smooth group is a torus as a group scheme. -/
theorem exists_groupIso (hc : IsNeronNGon E.curve 1 (by decide)) :
    ∃ e : (T) ≅ E.group, IsMonHom e.hom := by
  obtain ⟨p, q, h⟩ := hc
  exact ⟨pointedIso E p q h, pointedIso_isMonHom E p q h⟩

end FLT.Mazur.OneGonOriginalGroup
