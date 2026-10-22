/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonGeneralizedCurveActionExt

/-!
# Full generalized-curve comparison of polygon pinching realizations

The unique comparison of two pinching pushouts preserves the component tori.
Their canonical group is unchanged, so density identifies the whole actions.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonGeneralizedPinchingIso
open PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C D : Over (Spec (.of K))}
  (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (p' : components K n ⟶ D) (q' : nodes K n ⟶ D)
  (h' : IsPushout (toComponents K n hn) (toNodes K n) p' q')
local notation "E" => PolygonGeneralizedCurve.curve K n hn p q h
local notation "F" => PolygonGeneralizedCurve.curve K n hn p' q' h'

/-- The unique isomorphism of the original whole pinching pushouts. -/
def wholeIso : C ≅ D := h.isoIsPushout _ _ h'

omit [NeZero n] in
/-- The original normalization map is retained by the whole comparison. -/
@[reassoc] theorem normalization_wholeIso :
    p ≫ (wholeIso n hn p q h p' q' h').hom = p' :=
  h.inl_isoIsPushout_hom _ _ h'

omit [NeZero n] in
/-- The actual node section is retained as well. -/
@[reassoc] theorem nodes_wholeIso :
    q ≫ (wholeIso n hn p q h p' q' h').hom = q' :=
  h.inr_isoIsPushout_hom _ _ h'

/-- The comparison preserves the entire smooth inclusion on every torus component. -/
theorem inclusion_wholeIso :
    (E).inclusion ≫ (wholeIso n hn p q h p' q' h').hom = (F).inclusion := by
  let _ := polygon_lfp K n hn p q h
  let _ := polygon_lfp K n hn p' q' h'
  apply Sigma.hom_ext
  intro i
  have he : PolygonSplitGroup.component K n i ≫ (E).inclusion =
      torusToComponent K ≫ componentι K n ((ZMod.finEquiv n).symm i) ≫ p := by
    exact PolygonActionSmooth.component_smoothMap K n hn p q h i
  have hf : PolygonSplitGroup.component K n i ≫ (F).inclusion =
      torusToComponent K ≫ componentι K n ((ZMod.finEquiv n).symm i) ≫ p' := by
    exact PolygonActionSmooth.component_smoothMap K n hn p' q' h' i
  change PolygonSplitGroup.component K n i ≫ _ = _
  rw [← Category.assoc, he, hf]
  simp only [Category.assoc, normalization_wholeIso]

/-- Two pinching realizations give isomorphic full canonical generalized curves. -/
def generalizedIso : (E) ≅ (F) := by
  let g : (E).group ≅ (F).group := Iso.refl _
  let _ : IsMonHom g.hom :=
    inferInstanceAs (IsMonHom (𝟙 (PolygonSplitGroup.model K n)))
  apply PolygonGeneralizedCurve.isoOfInclusion K n hn p q h
    (wholeIso n hn p q h p' q' h') g
  change (E).inclusion ≫ (wholeIso n hn p q h p' q' h').hom =
    𝟙 (F).group ≫ (F).inclusion
  rw [Category.id_comp]
  exact inclusion_wholeIso n hn p q h p' q' h'

end FLT.Mazur.PolygonGeneralizedPinchingIso
