/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneCubicGroupPresentation

/-!
# Group comparison for any original pointed cubic presentation

The complete pointed isomorphism lifts along the actual coefficient spectrum
map. Relative rigidity identifies its group law with the established cubic law.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.FCurve
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{0}} [IsAffine S] (W : WeierstrassCurve Γ(S, ⊤))

/-- The established cubic carrier over the original affine base. -/
def pointedCubicBase : Over S := (Over.pullback S.toSpecΓ).obj (integralCurveOver W)

/-- The established cubic law pulled back along the actual canonical spectrum map. -/
@[instance_reducible] def pointedCubicBaseCommGrp [W.IsElliptic] :
    CommGrpObj (pointedCubicBase W) := by
  let _ := integralCurveCommGrpObj W (WeierstrassCurve.IsElliptic.isUnit (W := W))
  exact
    { __ := Functor.grpObjObj (F := Over.pullback S.toSpecΓ)
      __ := Functor.isCommMonObj_obj (F := Over.pullback S.toSpecΓ) }

variable (G : Over S) (e : G.left ≅ integralCurve W)
  (he : e.hom ≫ integralCurveStructure W = G.hom ≫ S.toSpecΓ)

/-- The original complete comparison as a morphism over the original base. -/
def pointedCubicBaseMap : G ⟶ pointedCubicBase W :=
  Over.homMk (pullback.lift e.hom G.hom he) (pullback.lift_snd _ _ _)

omit [IsAffine S] in
/-- Projection recovers the specified original complete cubic isomorphism. -/
@[reassoc] theorem pointedCubicBaseMap_fst :
    (pointedCubicBaseMap W G e he).left ≫
      pullback.fst (integralCurveStructure W) S.toSpecΓ = e.hom :=
  pullback.lift_fst _ _ _

/-- Lifting the original comparison along an affine spectrum isomorphism preserves invertibility. -/
instance pointedCubicBaseMap_isIso : IsIso (pointedCubicBaseMap W G e he) := by
  have : IsIso ((pointedCubicBaseMap W G e he).left ≫
      pullback.fst (integralCurveStructure W) S.toSpecΓ) := by
    rw [pointedCubicBaseMap_fst]
    infer_instance
  have : IsIso (pointedCubicBaseMap W G e he).left :=
    (isIso_comp_right_iff _ (pullback.fst
      (integralCurveStructure W) S.toSpecΓ)).mp inferInstance
  have : IsIso ((Over.forget S).map (pointedCubicBaseMap W G e he)) := this
  exact isIso_of_reflects_iso _ (Over.forget S)

variable [W.IsElliptic]
/-- Use the established pulled-back cubic operations in the comparison statements. -/
local instance : CommGrpObj (pointedCubicBase W) := pointedCubicBaseCommGrp W

/-- A specified zero section maps to the identity of the existing cubic group. -/
theorem pointedCubicBaseMap_zero (s : 𝟙_ (Over S) ⟶ G)
    (hs : s.left ≫ e.hom = S.toSpecΓ ≫ integralCurveZero W) :
    s ≫ pointedCubicBaseMap W G e he = η[pointedCubicBase W] := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (pullback.fst (integralCurveStructure W) S.toSpecΓ)).mp
  rw [Over.comp_left, Category.assoc, pointedCubicBaseMap_fst, hs]
  symm
  exact GroupSectionBaseChange.section_fst S.toSpecΓ (integralCurveOverZero W)

/-- Relative rigidity preserves the established group laws, including over nonreduced bases. -/
theorem pointedCubicBaseMap_isMonHom [IsLocallyNoetherian S] [GrpObj G]
    [IsProper G.hom] [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
    (hs : (η[G]).left ≫ e.hom = S.toSpecΓ ≫ integralCurveZero W) :
    IsMonHom (pointedCubicBaseMap W G e he) := by
  let _ : IsSeparated (pointedCubicBase W).hom :=
    inferInstanceAs (IsSeparated (pullback.snd (integralCurveStructure W) S.toSpecΓ))
  let _ : LocallyOfFiniteType (pointedCubicBase W).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd (integralCurveStructure W) S.toSpecΓ))
  exact properRelative_isMonHom_of_one G (pointedCubicBase W) _
    (pointedCubicBaseMap_zero W G e he η[G] hs)

end FLT.Mazur.FCurve
