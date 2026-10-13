/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveUnrestrictedCubicPresentation
public import FLT.Mazur.GeneralizedCurveLocalPointFrames
public import FLT.Mazur.GeneralizedCurveSmoothBaseCubic
public import FLT.Mazur.GeneralizedCurveSectionComposition

/-!
# Pointed cubic coverage over arbitrary original bases

Actual point-line frames give complete pointed cubic presentations on affine
neighborhoods. Restricting first to the smooth base locus and flattening the
base changes yields presentations of the original single changed curve.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve.UnrestrictedCubic
open FCurve WeierstrassIntegralChart GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{0}} (E : GeneralizedEllipticCurve S)

/-- Every original smooth curve has a pointed cubic inside any given base neighborhood. -/
theorem exists_local_pointedCubic [SmoothOfRelativeDimension 1 E.curve.hom]
    (s : 𝟙_ (Over S) ⟶ E.curve) {V : S.Opens} {x : S} (hx : x ∈ V) :
    ∃ U : S.affineOpens, x ∈ U.1 ∧ U.1 ≤ V ∧
      ∃ (W : WeierstrassCurve Γ(U.1.toScheme, ⊤)), W.IsElliptic ∧
        ∃ e : (E.baseChange U.1.ι).curve.left ≅ integralCurve W,
          e.hom ≫ integralCurveStructure W =
            (E.baseChange U.1.ι).curve.hom ≫ U.1.toScheme.toSpecΓ ∧
          (pullSection U.1.ι s).left ≫ e.hom =
            U.1.toScheme.toSpecΓ ≫ integralCurveZero W := by
  obtain ⟨U, hxU, hUV, ⟨e⟩⟩ := exists_smoothPoint_affineFrame E s hx
  let _ : IsAffine U.1.toScheme := U.2
  let E' := E.baseChange U.1.ι
  let t := pullSection U.1.ι s
  let _ := smoothCurve_geometricallyIntegral E'
  exact ⟨U, hxU, hUV, smoothPointCubicEquation E' t e,
    smoothPointCubicEquation_isElliptic E' t e, smoothPointCubicIso E' t e,
    smoothPointCubicIso_over E' t e, smoothPointCubicIso_marking E' t e⟩

/-- The local complete cubic presents the actual original single base change. -/
theorem exists_original_local_pointedCubic
    (s : 𝟙_ (Over S) ⟶ E.curve) {V : S.Opens} {x : S}
    (hx : x ∈ smoothBaseOpen E) (hxV : x ∈ V) :
    ∃ (T : Scheme) (_ : IsAffine T) (g : T ⟶ S),
      IsOpenImmersion g ∧ x ∈ Set.range g ∧ Set.range g ⊆ V ∧
        ∃ (W : WeierstrassCurve Γ(T, ⊤)), W.IsElliptic ∧
          ∃ e : (E.baseChange g).curve.left ≅ integralCurve W,
            e.hom ≫ integralCurveStructure W = (E.baseChange g).curve.hom ≫ T.toSpecΓ ∧
              (pullSection g s).left ≫ e.hom = T.toSpecΓ ≫ integralCurveZero W := by
  let B := smoothBaseOpen E
  obtain ⟨U, hxU, hUV, W, hW, e, he, hs⟩ :=
    exists_local_pointedCubic (E.baseChange B.ι) (pullSection B.ι s)
      (x := (⟨x, hx⟩ : B.toScheme)) (V := B.ι ⁻¹ᵁ V) hxV
  let g : U.1.toScheme ⟶ S := U.1.ι ≫ B.ι
  let c := ((forgetCurve (S := U.1.toScheme)) ⋙ Over.forget U.1.toScheme).mapIso
    (E.baseChangeCompIso B.ι U.1.ι)
  refine ⟨U.1.toScheme, U.2, g, inferInstance, ?_, ?_, W, hW, c ≪≫ e, ?_, ?_⟩
  · exact ⟨⟨⟨x, hx⟩, hxU⟩, rfl⟩
  · rintro _ ⟨y, rfl⟩
    exact hUV y.property
  · change c.hom ≫ e.hom ≫ integralCurveStructure W = _
    rw [he, ← Category.assoc]
    exact congrArg (fun k ↦ k ≫ U.1.toScheme.toSpecΓ)
      (E.baseChangeCompIso B.ι U.1.ι).hom.curve.w
  · change (pullSection g s).left ≫ c.hom ≫ e.hom = _
    rw [← Category.assoc]
    change ((pullSection (U.1.ι ≫ B.ι) s).left ≫
      (E.baseChangeCompIso B.ι U.1.ι).hom.curve.left) ≫ e.hom = _
    rw [baseChangeCompIso_section]
    exact hs

end FLT.Mazur.GeneralizedEllipticCurve.UnrestrictedCubic
