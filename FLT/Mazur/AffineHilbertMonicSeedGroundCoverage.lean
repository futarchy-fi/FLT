/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertMonicSeedGroundEtale

/-!
# Actual coverage retained by changed-ground seed selections

Every point of a selected seed chart whose translation coordinate has a new
lift survives in the constructed changed source. Applying the affine seed
point gives coverage through the original propagated branch point.
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
local instance monicSeedGroundCoverageSmooth : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "h" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "P" => variableHilbertFixedBaseProjection f a hL d V W t
variable {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  [Etale V.hom] [Etale W.hom]
  {Z : Scheme} (s : Z ⟶ A.left) [Etale s]
  [Etale (s ≫ (finiteKernelProjection f hL d V c k).left)]
  [Mono (s ≫ (finiteKernelProjection f hL d V c k).left)]
  (z : (pullback (snd f hL d V c k).left s : Scheme))
local notation "v" => monicSeedAffineMap f hL d V c k s z
local notation "k₀" => monicSeedAffineChart f hL d V c k s z
local notation "w₀" => finiteKernelProjection f hL d V c k
local notation "hw₀" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
local instance seedGroundCoverageSelectedOpen : IsOpenImmersion (k₀).left :=
  monicSeedAffineChart_isOpenImmersion f hL d V c k s z (w₀).left hw₀

local notation "B" => monicSeedGroundSource f a hL d V W t c k s z
local notation "u" => monicSeedGroundMap f a hL d V W t c k s z
local notation "l" => monicSeedGroundChart f a hL d V W t c k s z
local notation "x₀" => monicSeedAffinePoint f hL d V c k s z
local notation "b₀" => SchemeRelationEtaleBranchPropagation.branch
  (Over.Hom.left (fst f hL d V c k)) (Over.Hom.left (snd f hL d V c k)) s

omit [IsAffine A.left] [IsOpenImmersion k.left] [Etale V.hom] [Etale W.hom]
  [Etale s] [Etale (s ≫ (finiteKernelProjection f hL d V c k).left)]
  [Mono (s ≫ (finiteKernelProjection f hL d V c k).left)] in
/-- Compatible old chart and new translation points have an actual changed-source lift. -/
theorem monicSeedGround_exists_point
    (x : (monicSeedAffineSource f hL d V c k s z).left) (y : W.left)
    (hy : t.left y = (k₀ ≫ variableHilbertBase f d V).left x) :
    ∃ b : (B).left, (u).left b = (v).left x ∧
      (l ≫ variableHilbertBase q d W).left b = y := by
  obtain ⟨b, hb, hb'⟩ := Scheme.exists_preimage_of_isPullback
    (groundBaseSource_isPullback f a hL d V W t k₀) x y hy.symm
  refine ⟨b, ?_, hb'⟩
  change (v).left ((groundBaseSourceMap f a hL d V W t k₀).left b) = (v).left x
  exact congrArg (v).left hb

omit [IsAffine A.left] [IsOpenImmersion k.left] [Etale V.hom] [Etale W.hom]
  [Etale s] [Etale (s ≫ (finiteKernelProjection f hL d V c k).left)]
  [Mono (s ≫ (finiteKernelProjection f hL d V c k).left)] in
/-- The actual affine selection and base change preserve each original propagated branch point. -/
theorem monicSeedGround_exists_over_branch (y : W.left)
    (hy : t.left y = (k ≫ variableHilbertBase f d V).left (b₀ z)) :
    ∃ b : (B).left, (u).left b = b₀ z ∧
      (l ≫ variableHilbertBase q d W).left b = y := by
  have hx : (k₀ ≫ variableHilbertBase f d V).left x₀ =
      (k ≫ variableHilbertBase f d V).left (b₀ z) :=
    congrArg (variableHilbertBase f d V).left
      (monicSeedAffinePoint_chart f hL d V c k s z)
  obtain ⟨b, hb, hb'⟩ := monicSeedGround_exists_point
    f a hL d V W t c k s z x₀ y (hy.trans hx.symm)
  refine ⟨b, hb.trans ?_, hb'⟩
  exact SchemeRelationMonicSeedKernel.affinePoint_original
    (p := fst f hL d V c k) s z

omit [IsAffine A.left] [IsOpenImmersion k.left] [Etale V.hom] [Etale W.hom]
  [Etale s] [Etale (s ≫ (finiteKernelProjection f hL d V c k).left)]
  [Mono (s ≫ (finiteKernelProjection f hL d V c k).left)] in
/-- A surjective translation refinement loses no point of the selected original affine chart. -/
theorem monicSeedGround_range_of_surjective [Surjective t.left] :
    Set.range (u).left = Set.range (v).left := by
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨(groundBaseSourceMap f a hL d V W t k₀).left b, rfl⟩
  · rintro ⟨b, rfl⟩
    have ht : Function.Surjective t.left := (inferInstance : Surjective t.left).1
    obtain ⟨y, hy⟩ := ht ((k₀ ≫ variableHilbertBase f d V).left b)
    obtain ⟨b', hb', _⟩ := monicSeedGround_exists_point f a hL d V W t c k s z b y hy
    exact ⟨b', hb'⟩

variable [Etale a] [Etale t.left] [IsAffine V.left] [IsAffine W.left]
local notation "hu" => monicSeedGround_square f a hL d V W t c k s z
local notation "j" => fixedBaseJointProjection f a hL d V W t c k l u hu
attribute [local irreducible] relation fst snd finiteKernelProjection finiteKernelModel
  fixedBaseJointProjection fixedBaseJointTarget fixedBaseJointToOld fixedBaseJointToNew

/-- Each lifted original branch point belongs to the actual effective joint region. -/
theorem monicSeedGround_exists_effective_over_branch (y : W.left)
    (hy : t.left y = (k ≫ variableHilbertBase f d V).left (b₀ z)) :
    ∃ b : (B).left, (u).left b = b₀ z ∧
      (l ≫ variableHilbertBase q d W).left b = y ∧
      j b ∈ SchemeFppfTargetOpen.locus j := by
  let _ := monicSeedGroundJoint_etale f a hL d V W t c k s z
  obtain ⟨b, hb, hb'⟩ := monicSeedGround_exists_over_branch f a hL d V W t c k s z y hy
  refine ⟨b, hb, hb', ?_⟩
  rw [← SetLike.mem_coe, SchemeFppfTargetOpen.coe_locus, SchemeFlatTargetOpen.locus_top]
  exact ⟨⟨b, rfl⟩, trivial⟩

end FLT.Mazur.HilbertChart.AffineRestriction
