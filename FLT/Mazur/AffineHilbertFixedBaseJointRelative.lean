/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseJointModel

/-!
# Relative joint models over both original coefficient bases

Construct relative target maps to the old and newly selected finite models.
Both source triangles retain their actual coefficient and structure-sheaf maps.
No Cartesian target square or effective Picard quotient is assumed.
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
local instance jointKernelOldInvariantAlgebra : Algebra R
    (SchemeEffectiveEpiSections.compatibleFunctions p₀ q₀) :=
  (invariantCoefficientBase f hL d V c k).toAlgebra
/-- Use the actual changed coefficient base on its full invariant ring. -/
local instance jointKernelNewInvariantAlgebra : Algebra R'
    (SchemeEffectiveEpiSections.compatibleFunctions p₁ q₁) :=
  (invariantCoefficientBase q h d W c' l).toAlgebra
local notation "C₀" => finiteKernelCoefficientAlgebra f hL d V c k
local notation "C₁" => finiteKernelCoefficientAlgebra q h d W c' l

local notation "α" => fixedBaseOldFiniteCoefficients f a hL d V W t c k l u hu
local notation "β" => AlgHom.toRingHom (Subalgebra.val C₁)
local notation "J" => fixedBaseJointTarget f a hL d V W t c k l u hu
local notation "π" => fixedBaseJointProjection f a hL d V W t c k l u hu
local notation "r₀" => fixedBaseJointToOld f a hL d V W t c k l u hu
local notation "r₁" => fixedBaseJointToNew f a hL d V W t c k l u hu
local notation "M₀" => finiteKernelModel f hL d V c k
local notation "M₁" => finiteKernelModel q h d W c' l
local notation "v₁" => finiteKernelProjection q h d W c' l

/-- The target comparisons retain the actual changed coefficient base. -/
theorem fixedBaseJoint_base_condition : r₀ ≫ (M₀).hom = r₁ ≫ (M₁).hom ≫ a := by
  apply SchemeRelationJointModel.affine_hom_ext p₁ q₁ α β
  change π ≫ (r₀ ≫ (M₀).hom) = π ≫ (r₁ ≫ (M₁).hom ≫ a)
  rw [← Category.assoc, fixedBaseJointProjection_toOld, Category.assoc,
    (finiteKernelProjection f hL d V c k).w, ← Category.assoc π,
    fixedBaseJointProjection_toNew, ← Category.assoc, (v₁).w]
  exact u.w

/-- The joint target is an actual scheme over the new original coefficient base. -/
def fixedBaseJointOver : Over (Spec (.of R')) := Over.mk (r₁ ≫ (M₁).hom)

/-- The source projection retains its original relative structure. -/
def fixedBaseJointRelativeProjection : B ⟶ fixedBaseJointOver f a hL d V W t c k l u hu :=
  Over.homMk π (by
    change π ≫ (r₁ ≫ (M₁).hom) = B.hom
    rw [← Category.assoc, fixedBaseJointProjection_toNew]
    exact (v₁).w)

/-- The comparison to the newly computed finite model is relative over the new base. -/
def fixedBaseJointRelativeToNew :
    fixedBaseJointOver f a hL d V W t c k l u hu ⟶ M₁ := Over.homMk r₁ rfl

/-- The old finite model is also compared over its unchanged original base. -/
def fixedBaseJointRelativeToOld :
    (Over.map a).obj (fixedBaseJointOver f a hL d V W t c k l u hu) ⟶ M₀ :=
  Over.homMk r₀ (by
    change r₀ ≫ (M₀).hom = (r₁ ≫ (M₁).hom) ≫ a
    rw [Category.assoc]
    exact fixedBaseJoint_base_condition f a hL d V W t c k l u hu)
local notation "j" => fixedBaseJointRelativeProjection f a hL d V W t c k l u hu

/-- The actual relative projection retains the new finite model triangle. -/
@[reassoc]
theorem fixedBaseJointRelativeProjection_toNew :
    j ≫ fixedBaseJointRelativeToNew f a hL d V W t c k l u hu = v₁ :=
  Over.OverMorphism.ext (fixedBaseJointProjection_toNew f a hL d V W t c k l u hu)

end FLT.Mazur.HilbertChart.AffineRestriction
