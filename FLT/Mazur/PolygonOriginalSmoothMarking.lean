/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonGeneralizedCurve
public import FLT.Mazur.PolygonMarkedSections
public import FLT.Mazur.GeneralizedCurveSmoothMarking

/-!
# Every original smooth polygon marking has Laurent coordinates

Compare the two presentations of the actual smooth open, without identifying
their group laws. Every original group section is then one of the canonical
unit markings on a normalization component, even for a higher polygon.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonOriginalSmoothMarking
open PolygonPinching PolygonMarkedSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] (E : GeneralizedEllipticCurve (Spec (.of K)))
  (n : ℕ) [NeZero n] (hn : 0 < n)
  (p : components K n ⟶ E.curve) (q : nodes K n ⟶ E.curve)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

include h in
/-- Every point of the original smooth group is a unit marking on the given polygon. -/
theorem exists_sectionMap (s : 𝟙_ (Over (Spec (.of K))) ⟶ E.group) :
    ∃ (a : Kˣ) (i : Fin n), (s ≫ E.inclusion).left = sectionMap K n p a i := by
  let F := PolygonGeneralizedCurve.curve K n hn p q h
  let e : E.group ≅ F.group := E.smoothIso ≪≫ F.smoothIso.symm
  have he : e.hom ≫ F.inclusion = E.inclusion := by
    simp only [e, GeneralizedEllipticCurve.inclusion, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  obtain ⟨a, b, hab⟩ := PolygonGroupPoints.groupPoint_surjective K n (s ≫ e.hom)
  have hi : PolygonSplitGroup.component K n b ≫ F.inclusion =
      torusToComponent K ≫ componentι K n ((ZMod.finEquiv n).symm b) ≫ p := by
    change PolygonSplitGroup.component K n b ≫ PolygonActionSmooth.smoothMap K n hn p q h = _
    exact PolygonActionSmooth.component_smoothMap K n hn p q h b
  refine ⟨a, (ZMod.finEquiv n).symm b, ?_⟩
  have hz : s ≫ E.inclusion = PolygonActionTranslation.gmPoint K a ≫
      torusToComponent K ≫ componentι K n ((ZMod.finEquiv n).symm b) ≫ p := by
    rw [← he, ← Category.assoc, ← hab, Category.assoc]
    exact congrArg (PolygonActionTranslation.gmPoint K a ≫ ·) hi
  exact congrArg (fun f ↦ f.left) hz

end FLT.Mazur.PolygonOriginalSmoothMarking
