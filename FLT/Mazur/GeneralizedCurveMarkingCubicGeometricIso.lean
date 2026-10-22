/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingAffineCartesian
public import FLT.Mazur.GeneralizedCurveCoefficientGeometricFiber
public import FLT.Mazur.RelativeCommonOpenEulerBaseChange
public import FLT.Mazur.WeierstrassAffineGeometricIntegral
public import FLT.Mazur.WeierstrassGeometricIntegral
public import FLT.Mazur.WeierstrassGenusOneFamily

/-!
# The original cubic comparison on singular geometric fibers

The original affine comparison is Cartesian. After a geometric field test,
both integral curves have structure Euler characteristic zero. This proves
that the actual base-changed morphism is an isomorphism everywhere, including
at singular points, without whole-curve smoothness or a discriminant unit.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve WeierstrassIntegralChart ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle Scheme.Modules.pullback

variable {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) [GeometricallyIntegral E.curve.hom]
  (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

local instance generalizedCurveMarkingCubicGeometricIsoProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (Scheme.Modules.pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

local notation "L" => divisorLineBundle (Scheme.Hom.ker (Over.Hom.left (t))) (hI)
local notation "T" => smoothMarkingProjectiveSections E s e
local notation "W" => smoothMarkingWeierstrassCurve E s e
open WeierstrassIntegralChart

local notation "U" => (TopologicalSpace.Closeds.compl (Scheme.IdealSheafData.support
    (Scheme.Hom.ker (Over.Hom.left (t)))) : E.curve.left.Opens)

local notation "q" => E.curve.hom ≫ S.toSpecΓ
local notation "r" => integralCurveStructure (W)
local notation "f" => smoothMarkingToIntegralCubic E s e

/-- The original global comparison after a coefficient field test. -/
def smoothMarkingCubicFieldMap {K : Type} [Field K]
    (b : Spec (.of K) ⟶ Spec Γ(S, ⊤)) : pullback (q) b ⟶ pullback (r) b :=
  pullback.map _ _ _ _ (f) (𝟙 _) (𝟙 _)
    (by simpa using (smoothMarkingToIntegralCubic_over E s e).symm) (by simp)

/-- Every geometric coefficient test identifies the entire original integral-fiber curve. -/
theorem smoothMarkingCubicGeometricMap_isIso {K : Type} [Field K] [IsAlgClosed K]
    (b : Spec (.of K) ⟶ Spec Γ(S, ⊤)) : IsIso (smoothMarkingCubicFieldMap E s e b) := by
  let Q := smoothMarkingIntegralAffineIso E s e
  let j := Q.inv ≫ Scheme.Opens.ι (X := E.curve.left) (U)
  let k := integralCurveChart (W) 2
  have H : IsPullback (𝟙 _) j k (f) := by
    have hi : IsPullback (𝟙 _) Q.inv (𝟙 _) Q.hom :=
      IsPullback.of_horiz_isIso ⟨by simp⟩
    simpa only [Category.id_comp] using
      hi.paste_vert (smoothMarkingIntegralAffine_isPullback E s e)
  let _ : GeometricallyIntegral (q) :=
    (MorphismProperty.cancel_right_of_respectsIso @GeometricallyIntegral E.curve.hom
      S.toSpecΓ).mpr inferInstance
  have hu : IsIntegral (pullback (k ≫ (r)) b) := by
    change IsIntegral (pullback (integralCurveChart (W) 2 ≫ (r)) b)
    rw [integralCurveChart_structure]
    exact GeometricallyIntegral.geometrically_isIntegral b _ _ (.of_hasPullback _ _)
  let _ := hu
  apply commonOpen_euler_fieldBaseChange_isIso (q) (r) j k (f)
    (smoothMarkingToIntegralCubic_over E s e) H b (E.coefficientGeometricFiber_dimension b)
  rw [E.coefficientGeometricFiber_euler b]
  symm
  apply curveEulerCharacteristic_structure_zero
  · exact integralCurveFieldSquareH0_finrank (W) b _ _ (.of_hasPullback _ _)
  · exact integralCurveFieldSquareH1_finrank (W) b _ _ (.of_hasPullback _ _)

omit [GeometricallyIntegral E.curve.hom] in
/-- The geometric comparison retains the actual original morphism under projection. -/
@[reassoc] theorem smoothMarkingCubicFieldMap_fst {K : Type} [Field K]
    (b : Spec (.of K) ⟶ Spec Γ(S, ⊤)) :
    smoothMarkingCubicFieldMap E s e b ≫ pullback.fst (r) b =
      pullback.fst (q) b ≫ (f) := by
  simp [smoothMarkingCubicFieldMap]

end FLT.Mazur.GeneralizedEllipticCurve
