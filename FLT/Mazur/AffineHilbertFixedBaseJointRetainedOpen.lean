/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseJointEffectiveOpen
public import FLT.Mazur.MonomorphismRelativeOpenReselected

/-!
# Whole new kernel fibers retained from the old Picard inverse locus

The actual joint model retains every old inverse neighborhood relevant to its
new kernel, before removing whole bad target fibers. The resulting open
contains the transported old effective open, and all of its kernel tests lift
to the full changed Picard relation. Coverage remains a geometric task.
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
local notation "p₀" => Over.Hom.left (fst f hL d V c k)
local notation "q₀" => Over.Hom.left (snd f hL d V c k)
local notation "p₁" => Over.Hom.left (fst q h d W c' l)
local notation "q₁" => Over.Hom.left (snd q h d W c' l)
local notation "w" => finiteKernelProjection f hL d V c k
local notation "v" => fixedBaseJointRelativeProjection f a hL d V W t c k l u hu
local notation "b" => fixedBaseJointRelativeToOld f a hL d V W t c k l u hu
local notation "π" => fixedBaseJointProjection f a hL d V W t c k l u hu
local notation "H₀" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
local notation "H₁" => fixedBaseJointProjection_condition f a hL d V W t c k l u hu

local notation "Δ" => fixedBaseJointRelativeProjection_toOld f a hL d V W t c k l u hu
local notation "κ" => fixedBaseModelKernelMap a u w v b Δ
local notation "m₀" => modelRelationKernelMap f hL d V c k (Over.Hom.left w) H₀
local notation "m₁" => modelRelationKernelMap q h d W c' l π H₁
local notation "ρ" => Over.Hom.left (fixedBaseRelationMap f a hL d V W t c k l u hu)
local notation "Q" => pullback.fst π π ≫ π
local notation "HD" => fixedBaseModelRelationSquare_isPullback
  f a hL d V W t c k l u hu w v b Δ H₀ H₁

/-- Keep whole new fibers whose original kernel coordinates have old Picard arrows. -/
def fixedBaseJointRetainedTargetOpen :
    (fixedBaseJointTarget f a hL d V W t c k l u hu).Opens :=
  MonomorphismRelativeOpen.retainedTargetOpen m₀ κ Q
local notation "U" => fixedBaseJointRetainedTargetOpen f a hL d V W t c k l u hu

/-- Every transported old effective target neighborhood lies in the retained new region. -/
theorem fixedBaseJointRetainedTargetOpen_contains_old :
    (fixedBaseJointToOld f a hL d V W t c k l u hu) ⁻¹ᵁ
      KernelPairEffectiveOpen.targetOpen p₀ q₀ (w).left H₀ ≤ U :=
  MonomorphismRelativeOpen.preimage_targetOpen_le_retained m₀ κ Q
    (pullback.fst (w).left (w).left ≫ (w).left) (b).left
    (fixedBaseModelKernelMap_target a u w v b Δ)

/-- The full relation square proves effectivity on every retained new kernel fiber. -/
theorem fixedBaseJointRetainedTargetOpen_le_effective : U ≤
    fixedBaseJointEffectiveTargetOpen f a hL d V W t c k l u hu :=
  MonomorphismRelativeOpen.retainedTargetOpen_le m₀ κ Q ρ m₁ HD

set_option backward.isDefEq.respectTransparency false in
/-- All original arrows are recovered on this region, including nilpotent scheme tests. -/
theorem fixedBaseJointRetainedTargetOpen_lift {Z : Scheme} (x y : Z ⟶ B.left)
    (hxy : x ≫ π = y ≫ π) (hx : Set.range (x ≫ π) ⊆ U) :
    ∃! z : Z ⟶ (relation q h d W c' l).left, z ≫ p₁ = x ∧ z ≫ q₁ = y := by
  let j := pullback.lift x y hxy
  have hj : Set.range (j ≫ Q) ⊆ U := by
    simpa only [j, pullback.lift_fst_assoc] using hx
  obtain ⟨z, hz, huniq⟩ :=
    MonomorphismRelativeOpen.retainedTargetOpen_test_lift m₀ κ Q ρ m₁ HD j hj
  refine ⟨z, ⟨?_, ?_⟩, ?_⟩
  · simpa only [Category.assoc, modelRelationKernelMap_fst, j, pullback.lift_fst] using
      congrArg (fun t ↦ t ≫ pullback.fst π π) hz
  · simpa only [Category.assoc, modelRelationKernelMap_snd, j, pullback.lift_snd] using
      congrArg (fun t ↦ t ≫ pullback.snd π π) hz
  · intro z' hz'
    apply huniq z'
    change z' ≫ m₁ = j
    apply pullback.hom_ext (f := π) (g := π)
    · simpa only [Category.assoc, modelRelationKernelMap_fst, j, pullback.lift_fst] using hz'.1
    · simpa only [Category.assoc, modelRelationKernelMap_snd, j, pullback.lift_snd] using hz'.2

end FLT.Mazur.HilbertChart.AffineRestriction
