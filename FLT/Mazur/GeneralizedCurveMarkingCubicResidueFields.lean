/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingCubicFinite
public import FLT.Mazur.GeneralizedCurveMarkingPointedCubic
public import FLT.Mazur.SectionResidueFieldIso

/-!
# Residue fields of the original relative cubic morphism

The affine isomorphism preserves residue fields off the marking. At each
marked point the pointed identity and the section equations preserve them as
well. These computations hold over the original possibly nonreduced base.

This specialization assumes integral geometric fibers, allowing singular cubics
but excluding higher polygons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  Scheme.Modules.pullback ModuleSheafTensor.tensor

variable {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) [GeometricallyIntegral E.curve.hom]
  (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

local instance generalizedCurveMarkingCubicResidueFieldsProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

local notation "L" => divisorLineBundle (Scheme.Hom.ker (Over.Hom.left (t))) (hI)
local notation "T" => smoothMarkingProjectiveSections E s e
local notation "W" => smoothMarkingWeierstrassCurve E s e
open WeierstrassIntegralChart

local notation "U" => (TopologicalSpace.Closeds.compl (Scheme.IdealSheafData.support
    (Scheme.Hom.ker (Over.Hom.left (t)))) : E.curve.left.Opens)

local notation "f" => smoothMarkingToIntegralCubic E s e

omit [GeometricallyIntegral E.curve.hom] in
/-- At the original marking the global cubic map induces an isomorphism of residue fields. -/
theorem smoothMarkingToIntegralCubic_marking_residueField (a : S) :
    IsIso ((f).residueFieldMap ((t).left a)) := by
  let _ := section_residueFieldMap_isIso E.curve.hom (t).left (t).w a
  let _ := section_residueFieldMap_isIso (integralCurveStructure (W))
    (integralCurveZero (W)) (integralCurveZero_structure (W)) (S.toSpecΓ a)
  have hz : IsIso ((S.toSpecΓ ≫ integralCurveZero (W)).residueFieldMap a) := by
    rw [Scheme.residueFieldMap_comp]
    infer_instance
  have h : IsIso (((t).left ≫ (f)).residueFieldMap a) :=
    (congrArg (fun k : S ⟶ integralCurve (W) ↦ IsIso (k.residueFieldMap a))
      (smoothMarkingToIntegralCubic_marking E s e)).mpr hz
  rw [Scheme.residueFieldMap_comp] at h
  exact IsIso.of_isIso_comp_right _ ((t).left.residueFieldMap a)

/-- The actual cubic map preserves every residue field on the original total space. -/
theorem smoothMarkingToIntegralCubic_residueField (x : E.curve.left) :
    IsIso ((f).residueFieldMap x) := by
  by_cases hx : x ∈ (U)
  · let i := Scheme.Opens.ι (X := E.curve.left) (U)
    let a : (U) := ⟨x, hx⟩
    let _ := smoothMarkingToIntegralCubic_affine_isOpenImmersion E s e
    have h : IsIso ((i ≫ (f)).residueFieldMap a) := inferInstance
    rw [Scheme.residueFieldMap_comp] at h
    have hi : IsIso ((f).residueFieldMap (i a)) :=
      IsIso.of_isIso_comp_right _ (i.residueFieldMap a)
    exact hi
  · have hx' : x ∈ ((t).left.ker.support : Set E.curve.left) := not_not.mp hx
    rw [support_section_ker E.curve.hom (t).left (t).w] at hx'
    obtain ⟨a, rfl⟩ := hx'
    exact smoothMarkingToIntegralCubic_marking_residueField E s e a

end FLT.Mazur.GeneralizedEllipticCurve
