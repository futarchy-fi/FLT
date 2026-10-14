/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseJointRelative

/-!
# Relative joint models and their unchanged full candidate kernels

Both original bases are retained by actual target maps. The complete kernel
of the joint projection is isomorphic to the newly computed finite-model
kernel, including nilpotent structure. Neither kernel is identified with the
original Picard relation without a further geometric proof.
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
local instance jointTestOldInvariantAlgebra : Algebra R
    (SchemeEffectiveEpiSections.compatibleFunctions p₀ q₀) :=
  (invariantCoefficientBase f hL d V c k).toAlgebra
/-- Use the actual changed coefficient base on its full invariant ring. -/
local instance jointTestNewInvariantAlgebra : Algebra R'
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

attribute [local irreducible] finiteKernelCoefficientAlgebra fixedBaseOldFiniteCoefficients

local notation "j" => fixedBaseJointRelativeProjection f a hL d V W t c k l u hu

/-- Every relative scheme test detects exactly the full new invariant candidate kernel. -/
theorem fixedBaseJointRelativeProjection_test_iff {Z : Over (Spec (.of R'))} (x y : Z ⟶ B) :
    x ≫ j = y ≫ j ↔ x ≫ v₁ = y ≫ v₁ := by
  constructor
  · intro he
    simpa only [Category.assoc, fixedBaseJointRelativeProjection_toNew] using
      congrArg (fun z ↦ z ≫ fixedBaseJointRelativeToNew f a hL d V W t c k l u hu) he
  · intro he
    have hi := congrArg Over.Hom.left ((finiteKernelProjection_test_iff q h d W c' l x y).mp he)
    apply Over.OverMorphism.ext
    exact congrArg (fun z ↦ z ≫ SchemeRelationJointModel.fromInvariants p₁ q₁ α β) hi

end FLT.Mazur.HilbertChart.AffineRestriction
