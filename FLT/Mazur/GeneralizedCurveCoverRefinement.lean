/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveBaseChangeCompEq
public import FLT.Mazur.OverDirectedCoverGluing

/-!
# Full base-change comparisons retain the actual cover refinements

The canonical full-curve transports project to the transition morphisms of
the pulled-back open covers, for both the curve and its smooth group.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (C : S.OpenCover) [Category* C.I₀] [C.LocallyDirected]
  (E : GeneralizedEllipticCurve S) {i j : C.I₀} (h : i ⟶ j)

/-- Full transport along a cover refinement, with the original base maps. -/
def coverRefinementIso :
    E.baseChange (C.f i) ≅ (E.baseChange (C.f j)).baseChange (C.trans h) :=
  E.baseChangeCompEqIso (C.f j) (C.trans h) (C.f i) (C.trans_map h).symm

/-- The curve projection of full transport is the actual pulled-back cover transition. -/
@[reassoc] theorem coverRefinementIso_curve :
    (coverRefinementIso C E h).hom.curve.left ≫
      pullback.fst (E.baseChange (C.f j)).curve.hom (C.trans h) =
        Scheme.Cover.trans (C.pullback₁ E.curve.hom) h := by
  change _ = pullback.map E.curve.hom (C.f i) E.curve.hom (C.f j)
    (𝟙 _) (C.trans h) (𝟙 _) (by simp) (by simp)
  apply pullback.hom_ext
  · simpa only [coverRefinementIso, Category.assoc, pullback.lift_fst, Category.comp_id] using
      E.baseChangeCompEqIso_curve_fst (C.f j) (C.trans h) (C.f i) (C.trans_map h).symm
  · change (coverRefinementIso C E h).hom.curve.left ≫
        pullback.fst (pullback.snd E.curve.hom (C.f j)) (C.trans h) ≫
          pullback.snd E.curve.hom (C.f j) = _
    have hw := (coverRefinementIso C E h).hom.curve.w
    change (coverRefinementIso C E h).hom.curve.left ≫
      pullback.snd (pullback.snd E.curve.hom (C.f j)) (C.trans h) =
        pullback.snd E.curve.hom (C.f i) at hw
    rw [pullback.condition, ← Category.assoc, hw]
    simp only [pullback.lift_snd]

/-- The group projection retains the same actual cover refinement. -/
@[reassoc] theorem coverRefinementIso_group :
    (coverRefinementIso C E h).hom.group.left ≫
      pullback.fst (E.baseChange (C.f j)).group.hom (C.trans h) =
        Scheme.Cover.trans (C.pullback₁ E.group.hom) h := by
  change _ = pullback.map E.group.hom (C.f i) E.group.hom (C.f j)
    (𝟙 _) (C.trans h) (𝟙 _) (by simp) (by simp)
  apply pullback.hom_ext
  · simpa only [coverRefinementIso, Category.assoc, pullback.lift_fst, Category.comp_id] using
      E.baseChangeCompEqIso_group_fst (C.f j) (C.trans h) (C.f i) (C.trans_map h).symm
  · change (coverRefinementIso C E h).hom.group.left ≫
        pullback.fst (pullback.snd E.group.hom (C.f j)) (C.trans h) ≫
          pullback.snd E.group.hom (C.f j) = _
    have hw := (coverRefinementIso C E h).hom.group.w
    change (coverRefinementIso C E h).hom.group.left ≫
      pullback.snd (pullback.snd E.group.hom (C.f j)) (C.trans h) =
        pullback.snd E.group.hom (C.f i) at hw
    rw [pullback.condition, ← Category.assoc, hw]
    simp only [pullback.lift_snd]

end FLT.Mazur.GeneralizedEllipticCurve
