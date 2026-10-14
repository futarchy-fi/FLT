/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseJointTests
public import FLT.Mazur.KernelPairTestIso

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
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of R') ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) (W : Over (Spec (.of R')))
  (t : (Over.map a).obj W ⟶ V) (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "q" => Limits.pullback.snd f a
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
local instance : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "h" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "P" => variableHilbertFixedBaseProjection f a hL d V W t
variable {A : Over (Spec (.of R))} {B : Over (Spec (.of R'))}
  (k : A ⟶ variableHilbertTest f d V) (l : B ⟶ variableHilbertTest (Limits.pullback.snd f a) d W)
  (u : (Over.map a).obj B ⟶ A) (hu : u ≫ k = (Over.map a).map l ≫
    variableHilbertFixedBaseProjection f a hL d V W t)

variable [Etale V.hom] [Etale W.hom] [IsAffine A.left] [IsAffine B.left]
  [IsOpenImmersion k.left] [IsOpenImmersion l.left]
local notation "v₁" => finiteKernelProjection q h d W c' l
local notation "j" => fixedBaseJointRelativeProjection f a hL d V W t c k l u hu

/-- The complete scheme kernel, not only its points or its reduction, is retained. -/
def fixedBaseJointKernelIso : pullback j j ≅ pullback v₁ v₁ :=
  KernelPairTestIso.iso j v₁
    (fun x y ↦ fixedBaseJointRelativeProjection_test_iff f a hL d V W t c k l u hu x y)

/-- The full first source coordinate is retained by the constructed kernel isomorphism. -/
@[reassoc]
theorem fixedBaseJointKernelIso_fst :
    (fixedBaseJointKernelIso f a hL d V W t c k l u hu).hom ≫ pullback.fst v₁ v₁ =
      pullback.fst j j := KernelPairTestIso.hom_fst j v₁ _

/-- The independent second source coordinate is retained as well. -/
@[reassoc]
theorem fixedBaseJointKernelIso_snd :
    (fixedBaseJointKernelIso f a hL d V W t c k l u hu).hom ≫ pullback.snd v₁ v₁ =
      pullback.snd j j := KernelPairTestIso.hom_snd j v₁ _

end FLT.Mazur.HilbertChart.AffineRestriction
