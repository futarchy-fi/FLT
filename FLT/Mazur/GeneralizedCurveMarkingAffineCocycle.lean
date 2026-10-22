/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingAffineOverlap

/-!
# Cocycle on affine pieces of actual triple intersections

Three independently framed affine opens give compatible cubic transitions on
every common affine subopen. The original base can be nonaffine and nonseparated.
The transition from a chart to itself is the identity on its whole cubic.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback smoothMarkingWeierstrassCurve smoothMarkingTransportedFrame
variable {S : Scheme} [IsLocallyNoetherian S] (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group) (U V Z W : S.Opens)
  [IsAffine U.toScheme] [IsAffine V.toScheme] [IsAffine Z.toScheme] [IsAffine W.toScheme]
  (hU : W ≤ U) (hV : W ≤ V) (hZ : W ≤ Z)
  (a : SmoothMarkingFrame (E.baseChange U.ι) (pullSection U.ι s))
  (b : SmoothMarkingFrame (E.baseChange V.ι) (pullSection V.ι s))
  (c : SmoothMarkingFrame (E.baseChange Z.ι) (pullSection Z.ι s))

local instance affineCocycleNoetherian (X : S.Opens) [IsAffine X.toScheme] :
    IsNoetherianRing Γ(X.toScheme, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

omit [IsAffine U.toScheme] [IsAffine V.toScheme] [IsAffine Z.toScheme] in
/-- The independently constructed transitions obey the triple-intersection cocycle. -/
theorem smoothMarkingAffineOverlapIso_comp :
    smoothMarkingAffineOverlapIso E s U V W hU hV a b ≪≫
      smoothMarkingAffineOverlapIso E s V Z W hV hZ b c =
        smoothMarkingAffineOverlapIso E s U Z W hU hZ a c := by
  unfold smoothMarkingAffineOverlapIso
  exact smoothMarkingOverlapCubicIso_comp E U.ι V.ι Z.ι
    (S.homOfLE hU) (S.homOfLE hV) (S.homOfLE hZ) _ _ s _ _ _

omit [IsAffine U.toScheme] in
/-- The constructed self-transition on an actual affine overlap is the identity. -/
theorem smoothMarkingAffineOverlapIso_refl :
    smoothMarkingAffineOverlapIso E s U U W hU hU a a =
      Iso.refl (integralCurve (smoothMarkingOpenRestrictionEquation E s U W hU a)) := by
  have he : (baseChangeSquare U.ι U.ι (S.homOfLE hU) (S.homOfLE hU)
      (smoothMarkingOpenOverlap_square U U W hU hU)).app E =
        Iso.refl ((E.baseChange U.ι).baseChange (S.homOfLE hU)) := by
    apply Iso.ext
    apply E.baseChange_twice_hom_ext U.ι (S.homOfLE hU)
    change _ = 𝟙 _ ≫ _
    rw [smoothMarkingOverlap_projection, Category.id_comp]
  unfold smoothMarkingAffineOverlapIso smoothMarkingOverlapCubicIso
  simp only [he]
  exact markedCubicComparison_refl _ _ _

end FLT.Mazur.GeneralizedEllipticCurve
