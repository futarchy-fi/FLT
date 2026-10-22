/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingDirectRestriction
public import FLT.Mazur.GeneralizedCurveOpenRestrictionMap

/-!
# Functor laws for independently framed direct cubic charts

The actual original whole-curve maps detect the identity and composition laws.
The frames on all three affine opens are independent, and the original base
need not be affine or separated.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback smoothMarkingWeierstrassCurve smoothMarkingDirectRestriction
variable {S : Scheme} [IsLocallyNoetherian S] (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group) (U V W : S.Opens)
  [IsAffine U.toScheme] [IsAffine V.toScheme] [IsAffine W.toScheme]
  (a : SmoothMarkingFrame (E.baseChange U.ι) (pullSection U.ι s))
  (b : SmoothMarkingFrame (E.baseChange V.ι) (pullSection V.ι s))
  (c : SmoothMarkingFrame (E.baseChange W.ι) (pullSection W.ι s))

local instance directCocycleNoetherian (X : S.Opens) [IsAffine X.toScheme] :
    IsNoetherianRing Γ(X.toScheme, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

omit [IsAffine V.toScheme] in
/-- The direct cubic map commutes with the canonical whole-family restriction. -/
@[reassoc] theorem smoothMarkingDirectRestriction_curve (h : W ≤ U) :
    smoothMarkingToIntegralCubic (E.baseChange W.ι) (pullSection W.ι s) c ≫
      smoothMarkingDirectRestriction E s U W h a c =
        openRestrictionCurveMap E U W h ≫
          smoothMarkingToIntegralCubic (E.baseChange U.ι) (pullSection U.ι s) a := by
  rw [smoothMarkingDirectRestriction_whole, openRestrictionCurveMap, Category.assoc]

omit [IsAffine V.toScheme] [IsAffine W.toScheme] in
/-- The self-inclusion acts identically on the directly framed cubic. -/
theorem smoothMarkingDirectRestriction_refl :
    smoothMarkingDirectRestriction E s U U le_rfl a a = 𝟙 _ := by
  apply smoothMarkingToIntegralCubic_hom_ext (E.baseChange U.ι) (pullSection U.ι s) a
    (integralCurveStructure (smoothMarkingWeierstrassCurve
      (E.baseChange U.ι) (pullSection U.ι s) a))
  · rw [smoothMarkingDirectRestriction_over, Scheme.homOfLE_rfl,
      Scheme.Hom.id_appTop, Spec.map_id]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · rw [smoothMarkingDirectRestriction_curve, openRestrictionCurveMap_refl,
      Category.id_comp, Category.comp_id]

/-- Direct cubic restrictions satisfy composition for three independent frames. -/
theorem smoothMarkingDirectRestriction_comp (h : W ≤ V) (k : V ≤ U) :
    smoothMarkingDirectRestriction E s V W h b c ≫
      smoothMarkingDirectRestriction E s U V k a b =
        smoothMarkingDirectRestriction E s U W (h.trans k) a c := by
  apply smoothMarkingToIntegralCubic_hom_ext (E.baseChange W.ι) (pullSection W.ι s) c
    (integralCurveStructure (smoothMarkingWeierstrassCurve
      (E.baseChange U.ι) (pullSection U.ι s) a))
  · rw [Category.assoc, smoothMarkingDirectRestriction_over,
      ← Category.assoc, smoothMarkingDirectRestriction_over,
      smoothMarkingDirectRestriction_over, Category.assoc,
      ← Spec.map_comp, ← Scheme.Hom.comp_appTop, Scheme.homOfLE_homOfLE]
  · rw [← Category.assoc, smoothMarkingDirectRestriction_curve,
      Category.assoc, smoothMarkingDirectRestriction_curve,
      smoothMarkingDirectRestriction_curve, ← Category.assoc,
      openRestrictionCurveMap_comp]

end FLT.Mazur.GeneralizedEllipticCurve
