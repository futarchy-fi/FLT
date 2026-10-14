/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseJointFppfOpen
public import FLT.Mazur.AffineHilbertModelEtaleNeighborhoods

/-!
# Etale finite neighborhoods for actual joint Picard reselections

Both original finite coefficient maps survive in constructed finite etale
neighborhood diagrams. The joint effective fppf projection is proved etale;
no flatness or unramifiedness premise is imposed on the joint model itself.
This constructs neighborhoods of retained points, not global coverage.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
set_option backward.isDefEq.respectTransparency false
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
local instance jointEtaleNeighborhoodSmooth : SmoothOfRelativeDimension 1 q :=
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
local notation "v" => fixedBaseJointRelativeProjection f a hL d V W t c k l u hu
local notation "H" => fixedBaseJointProjection_condition f a hL d V W t c k l u hu
local instance jointEtaleNeighborhoodFinitePresentation : LocallyOfFinitePresentation (v).left :=
  fixedBaseJointProjection_locallyOfFinitePresentation f a hL d V W t c k l u hu

local notation "E" => fixedBaseJointFppfTarget f a hL d V W t c k l u hu
local notation "C" => modelFppfSource q h d W c' l v H
local notation "π" => fixedBaseJointFppfProjection f a hL d V W t c k l u hu
local notation "i" => fixedBaseJointFppfToModel f a hL d V W t c k l u hu
local notation "r₀" => fixedBaseJointToOld f a hL d V W t c k l u hu
local notation "r₁" => fixedBaseJointToNew f a hL d V W t c k l u hu
local notation "j" => modelFppfToEffective q h d W c' l v H ≫
  modelEffectiveToSource q h d W c' l v H

/-- Reselection retains the derived etale geometry on the complete joint fppf source. -/
instance fixedBaseJointFppfProjection_etale : Etale (π).left :=
  modelFppfProjection_etale q h d W c' l v H

/-- Finite etale branch diagrams keep both original finite coefficient morphisms literally. -/
theorem fixedBaseJoint_exists_finite_etale_neighborhood (x : (C).left) :
    ∃ (Z N : Over (Spec (.of R'))) (b : N ⟶ E) (s : Z ⟶ N) (e : Z ⟶ C) (z : Z.left),
      IsAffine Z.left ∧ IsAffine N.left ∧ Etale b.left ∧ Etale s.left ∧
        IsFinite s.left ∧ Surjective s.left ∧ Etale e.left ∧ e ≫ π = s ≫ b ∧
        e.left z = x ∧
        e.left ≫ (j).left ≫ u.left ≫ (finiteKernelProjection f hL d V c k).left =
          s.left ≫ b.left ≫ (i).left ≫ r₀ ∧
        e.left ≫ (j).left ≫ (finiteKernelProjection q h d W c' l).left =
          s.left ≫ b.left ≫ (i).left ≫ r₁ := by
  obtain ⟨Z, N, b, s, e, z, hZ, hN, hb, hs, hf, hsur, he, hsq, hz, _, _⟩ :=
    EtaleFiniteBranchTargetNeighborhood.exists_cover π ⊤ ⊤ x (by trivial) (by trivial)
  have Hsq := modelFppfOriginal_isPullback q h d W c' l v H
  have hbase : (j).left ≫ (v).left = (π).left ≫ (i).left := Hsq.w
  have hleft : e.left ≫ (π).left = s.left ≫ b.left := congrArg Over.Hom.left hsq
  have hsq' : e.left ≫ (j).left ≫ (v).left =
      s.left ≫ b.left ≫ (i).left := by
    rw [hbase, ← Category.assoc, hleft, Category.assoc]
  refine ⟨Z, N, b, s, e, z, hZ, hN, hb, hs, hf, hsur, he, hsq, hz, ?_, ?_⟩
  · have hc := congrArg (fun r ↦ r ≫ r₀) hsq'
    simpa only [Category.assoc, fixedBaseJointRelativeProjection,
      Over.homMk_left, fixedBaseJointProjection_toOld] using hc
  · have hc := congrArg (fun r ↦ r ≫ r₁) hsq'
    simpa only [Category.assoc, fixedBaseJointRelativeProjection,
      Over.homMk_left, fixedBaseJointProjection_toNew] using hc

end FLT.Mazur.HilbertChart.AffineRestriction
