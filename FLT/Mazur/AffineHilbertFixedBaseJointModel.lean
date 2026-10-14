/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseInvariants
public import FLT.Mazur.AffineHilbertFiniteKernelModel
public import FLT.Mazur.SchemeRelationJointModelGeometry

/-!
# Joint finite models after actual Picard translation refinement

Recompute the full new invariant kernel and adjoin the old finite coefficients
pulled back through the actual changed source. This constructs a Noetherian
model comparing both finite targets. It does not assume a Cartesian target
square, flatness, or equality of the invariant kernel with the Picard relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open FCurve CartierAbel SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of R') ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) (W : Over (Spec (.of R')))
  (t : (Over.map a).obj W ⟶ V) (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "q" => Limits.pullback.snd f a
local instance : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "h" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "P" => variableHilbertFixedBaseProjection f a hL d V W t
variable {A : Over (Spec (.of R))} {B : Over (Spec (.of R'))}
  (k : A ⟶ variableHilbertTest f d V) (l : B ⟶ variableHilbertTest (Limits.pullback.snd f a) d W)
  (u : (Over.map a).obj B ⟶ A) (hu : u ≫ k = (Over.map a).map l ≫
    variableHilbertFixedBaseProjection f a hL d V W t)

local notation "p₀" => Over.Hom.left (fst f hL d V c k)
local notation "q₀" => Over.Hom.left (snd f hL d V c k)
local notation "p₁" => Over.Hom.left (fst q h d W c' l)
local notation "q₁" => Over.Hom.left (snd q h d W c' l)
variable [Etale V.hom] [Etale W.hom] [IsAffine A.left] [IsAffine B.left]
  [IsOpenImmersion k.left] [IsOpenImmersion l.left]
/-- Use the actual old coefficient base on its full invariant ring. -/
local instance oldInvariantAlgebra : Algebra R
    (SchemeEffectiveEpiSections.compatibleFunctions p₀ q₀) :=
  (invariantCoefficientBase f hL d V c k).toAlgebra
/-- Use the actual changed coefficient base on its full invariant ring. -/
local instance newInvariantAlgebra : Algebra R'
    (SchemeEffectiveEpiSections.compatibleFunctions p₁ q₁) :=
  (invariantCoefficientBase q h d W c' l).toAlgebra
local notation "C₀" => finiteKernelCoefficientAlgebra f hL d V c k
local notation "C₁" => finiteKernelCoefficientAlgebra q h d W c' l

/-- The old finite coefficients become actual invariants of the full changed relation. -/
def fixedBaseOldFiniteCoefficients :
    C₀ →+* SchemeEffectiveEpiSections.compatibleFunctions p₁ q₁ :=
  (fixedBaseInvariantPullback f a hL d V W t c k l u hu).comp (C₀).val.toRingHom
local notation "α" => fixedBaseOldFiniteCoefficients f a hL d V W t c k l u hu
local notation "β" => AlgHom.toRingHom (Subalgebra.val C₁)

/-- A newly constructed finite target retaining old and new invariant coefficients. -/
def fixedBaseJointTarget : Scheme := SchemeRelationJointModel.target p₁ q₁ α β

/-- The source projection to the joint target is built from its original functions. -/
def fixedBaseJointProjection : B.left ⟶ fixedBaseJointTarget f a hL d V W t c k l u hu :=
  SchemeRelationJointModel.projection p₁ q₁ α β

/-- The joint target maps to the original finite model. -/
def fixedBaseJointToOld : fixedBaseJointTarget f a hL d V W t c k l u hu ⟶
    (finiteKernelModel f hL d V c k).left := SchemeRelationJointModel.toLeft p₁ q₁ α β

/-- The joint target also maps to the recomputed finite model of the changed chart. -/
def fixedBaseJointToNew : fixedBaseJointTarget f a hL d V W t c k l u hu ⟶
    (finiteKernelModel q h d W c' l).left := SchemeRelationJointModel.toRight p₁ q₁ α β

/-- The first triangle retains the actual old source comparison and coefficient map. -/
@[reassoc]
theorem fixedBaseJointProjection_toOld :
    fixedBaseJointProjection f a hL d V W t c k l u hu ≫
      fixedBaseJointToOld f a hL d V W t c k l u hu =
        u.left ≫ (finiteKernelProjection f hL d V c k).left := by
  change SchemeRelationJointModel.projection p₁ q₁ α β ≫
    SchemeRelationJointModel.toLeft p₁ q₁ α β = _
  rw [SchemeRelationJointModel.projection_toLeft]
  change B.left.toSpecΓ ≫ Spec.map _ = u.left ≫ (A.left.toSpecΓ ≫ Spec.map _)
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  rfl

/-- The second triangle retains all coefficients of the new full invariant kernel. -/
@[reassoc]
theorem fixedBaseJointProjection_toNew :
    fixedBaseJointProjection f a hL d V W t c k l u hu ≫
      fixedBaseJointToNew f a hL d V W t c k l u hu =
        (finiteKernelProjection q h d W c' l).left :=
  SchemeRelationJointModel.projection_toRight p₁ q₁ α β

/-- Noetherianity is proved for the newly constructed target. -/
instance fixedBaseJointTarget_isNoetherian :
    IsNoetherian (fixedBaseJointTarget f a hL d V W t c k l u hu) := by
  have h₀ : Algebra.FiniteType ℤ C₀ :=
    Algebra.FiniteType.trans (R := ℤ) (S := R) (A := C₀) inferInstance inferInstance
  have h₁ : Algebra.FiniteType ℤ C₁ :=
    Algebra.FiniteType.trans (R := ℤ) (S := R') (A := C₁) inferInstance inferInstance
  exact @SchemeRelationJointModel.isNoetherian _ _ p₁ q₁ C₀ C₁ _ _ α β h₀ h₁

/-- Affineness is likewise supplied by the construction, not a quotient hypothesis. -/
instance fixedBaseJointTarget_isAffine :
    IsAffine (fixedBaseJointTarget f a hL d V W t c k l u hu) :=
  inferInstanceAs (IsAffine (SchemeRelationJointModel.target p₁ q₁ α β))

/-- Finite presentation of the actual source projection to the newly constructed target. -/
instance fixedBaseJointProjection_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (fixedBaseJointProjection f a hL d V W t c k l u hu) := by
  have h₀ : Algebra.FiniteType ℤ C₀ :=
    Algebra.FiniteType.trans (R := ℤ) (S := R) (A := C₀) inferInstance inferInstance
  have h₁ : Algebra.FiniteType ℤ C₁ :=
    Algebra.FiniteType.trans (R := ℤ) (S := R') (A := C₁) inferInstance inferInstance
  have ht : LocallyOfFiniteType (SchemeRelationJointModel.coefficientProjection p₁ q₁ β) :=
    inferInstanceAs (LocallyOfFiniteType (finiteKernelProjection q h d W c' l).left)
  exact @SchemeRelationJointModel.projection_locallyOfFinitePresentation
    _ _ p₁ q₁ C₀ C₁ _ _ α β h₀ h₁ ht

/-- The unchanged complete Picard relation is coequalized by the new model. -/
@[reassoc]
theorem fixedBaseJointProjection_condition :
    p₁ ≫ fixedBaseJointProjection f a hL d V W t c k l u hu =
      q₁ ≫ fixedBaseJointProjection f a hL d V W t c k l u hu :=
  SchemeRelationJointModel.projection_condition p₁ q₁ α β

end FLT.Mazur.HilbertChart.AffineRestriction
