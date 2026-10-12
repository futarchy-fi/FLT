/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneCubicFinite
public import FLT.Mazur.RelativeGenusOnePointedCubic
public import FLT.Mazur.SectionResidueFieldIso

/-!
# Residue fields of the original relative cubic morphism

The affine isomorphism preserves residue fields off the marking. At each
marked point the pointed identity and the section equations preserve them as
well. These computations hold over the original possibly nonreduced base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates

variable {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

local notation "L" => divisorLineBundle s.left.ker hI
local notation "T" => relativePointProjectiveSections G hg s hI e
local notation "W" => relativePointWeierstrassCurve G hg s hI e
open WeierstrassIntegralChart

local notation "U" => (s.left.ker.support.compl : G.left.Opens)

local notation "f" => relativePointToIntegralCubic G hg s hI e

/-- At the original marking the global cubic map induces an isomorphism of residue fields. -/
theorem relativePointToIntegralCubic_marking_residueField (a : S) :
    IsIso ((f).residueFieldMap (s.left a)) := by
  let _ := section_residueFieldMap_isIso G.hom s.left s.w a
  let _ := section_residueFieldMap_isIso (integralCurveStructure (W))
    (integralCurveZero (W)) (integralCurveZero_structure (W)) (S.toSpecΓ a)
  have hz : IsIso ((S.toSpecΓ ≫ integralCurveZero (W)).residueFieldMap a) := by
    rw [Scheme.residueFieldMap_comp]
    infer_instance
  have h : IsIso ((s.left ≫ (f)).residueFieldMap a) :=
    (congrArg (fun k : S ⟶ integralCurve (W) ↦ IsIso (k.residueFieldMap a))
      (relativePointToIntegralCubic_marking G hg s hI e)).mpr hz
  rw [Scheme.residueFieldMap_comp] at h
  exact IsIso.of_isIso_comp_right _ (s.left.residueFieldMap a)

/-- The actual cubic map preserves every residue field on the original total space. -/
theorem relativePointToIntegralCubic_residueField (x : G.left) :
    IsIso ((f).residueFieldMap x) := by
  by_cases hx : x ∈ (U)
  · let i := Scheme.Opens.ι (X := G.left) (U)
    let a : (U) := ⟨x, hx⟩
    let _ := relativePointToIntegralCubic_affine_isOpenImmersion G hg s hI e
    have h : IsIso ((i ≫ (f)).residueFieldMap a) := inferInstance
    rw [Scheme.residueFieldMap_comp] at h
    have hi : IsIso ((f).residueFieldMap (i a)) :=
      IsIso.of_isIso_comp_right _ (i.residueFieldMap a)
    exact hi
  · have hx' : x ∈ (s.left.ker.support : Set G.left) := not_not.mp hx
    rw [support_section_ker G.hom s.left s.w] at hx'
    obtain ⟨a, rfl⟩ := hx'
    exact relativePointToIntegralCubic_marking_residueField G hg s hI e a

end FLT.Mazur.FCurve
