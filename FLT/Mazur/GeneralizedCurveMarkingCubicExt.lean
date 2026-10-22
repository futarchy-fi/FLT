/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveGroupFiniteness
public import FLT.Mazur.GeneralizedCurveMarkingFrameAffineChange
public import FLT.Mazur.WeierstrassAffineMorphismExt

/-!
# The original cubic map detects separated morphisms

The actual marking complement maps schematically densely to the cubic's affine
chart: its coordinate algebra is the full ring of complement functions. Thus
agreement after the whole original cubic map detects equality, even for higher
polygons. No assertion that the complement or whole curve is affine is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory TopologicalSpace
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback smoothMarkingWeierstrassCurve smoothMarkingChartRingEquiv
variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)
  (a : (pullback (s ≫ E.inclusion).left).obj
    (divisorLineBundle (s ≫ E.inclusion).left.ker
      (smoothMarking_relativeCartier E s).1) ≅ structureModule S)
local notation "W" => smoothMarkingWeierstrassCurve E s a
local notation "U" => TopologicalSpace.Closeds.compl (Scheme.IdealSheafData.support
  (Scheme.Hom.ker (Over.Hom.left (s ≫ E.inclusion))))

/-- The actual affine restriction is schematically dominant, retaining nilpotents. -/
theorem smoothMarkingToIntegralAffineChart_dominant :
    IsSchemeTheoreticallyDominant (smoothMarkingToIntegralAffineChart E s a) := by
  let _ : IsLocallyNoetherian S := isLocallyNoetherian_of_isOpenImmersion S.isoSpec.hom
  let _ : IsNoetherian S := ⟨⟩
  let _ := E.curve_isNoetherian
  let X := Scheme.Opens.toScheme (X := E.curve.left) (U)
  let _ : NoetherianSpace X :=
    (Scheme.Opens.ι (X := E.curve.left) (U)).isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  let _ : IsSchemeTheoreticallyDominant X.toSpecΓ := ⟨Scheme.ker_toSpecΓ X⟩
  let q := (smoothMarkingChartRingEquiv E s a).toCommRingCatIso
  change IsSchemeTheoreticallyDominant (X.toSpecΓ ≫ (Scheme.Spec.mapIso q.op).hom)
  infer_instance

/-- Agreement after the actual whole-curve cubic map determines a separated morphism. -/
theorem smoothMarkingToIntegralCubic_hom_ext {Y B : Scheme} (p : Y ⟶ B) [IsSeparated p]
    (f g : integralCurve (W) ⟶ Y) (hb : f ≫ p = g ≫ p)
    (hh : smoothMarkingToIntegralCubic E s a ≫ f =
      smoothMarkingToIntegralCubic E s a ≫ g) : f = g := by
  apply integralCurve_hom_ext_affine (W) p f g hb
  let _ := smoothMarkingToIntegralAffineChart_dominant E s a
  apply Chow.schematicallyDense_ext p
    (by simpa only [Category.assoc] using congrArg (integralCurveChart (W) 2 ≫ ·) hb)
    (smoothMarkingToIntegralAffineChart E s a)
  simpa only [← Category.assoc, smoothMarkingToIntegralAffineChart_cubic] using
    congrArg (Scheme.Opens.ι (X := E.curve.left) (U) ≫ ·) hh

end FLT.Mazur.GeneralizedEllipticCurve
