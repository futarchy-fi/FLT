/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertOldEnvelopeTarget
public import FLT.Mazur.AffineHilbertAdmissibleKernelOpen
public import FLT.Mazur.KernelPairEffectiveOpen

/-!
# Full original relation inverses over the old envelope target

Constructed old coefficients cover every original source point over the
whole-envelope target. Their old-kernel inverses yield effectivity on that
entire target open, without integral, flat, or generic-point assumptions.
Arbitrary scheme tests retain their unique original relation arrows.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "v" => Over.Hom.left (finiteKernelProjection f hL d V c k)
local notation "h" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "m" => pullback.lift p q h
local notation "b" => pullback.fst v v ≫ v
local notation "K" => (pullback v v : Scheme)
local notation "W" => oldEnvelopeTarget f hL d V c k
local instance oldEnvelopeKernelMono : Mono m := modelRelationKernelMap_mono f hL d V c k v h

/-- All original kernel points over this target have genuine local original inverse maps. -/
theorem oldEnvelopeTarget_kernel_le_inverse : b ⁻¹ᵁ W ≤ MonomorphismOpenImage.locus m := by
  intro z hz
  obtain ⟨r, hr, hx⟩ := oldEnvelopeTarget_source_coefficient f hL d V c k
    (pullback.fst v v z) hz
  exact admissibleOriginalKernel_le_inverseLocus f hL d V c k
    (oldTargetInvariantCoefficient f hL d V c k r) hr hx

/-- The full old envelope target lies in the effective old target, including all kernel branches. -/
theorem oldEnvelopeTarget_le_effective : W ≤ KernelPairEffectiveOpen.targetOpen p q v h :=
  SchemeWholeFiberOpen.le_locus b (MonomorphismOpenImage.locus m) W
    (oldEnvelopeTarget_kernel_le_inverse f hL d V c k)

/-- A constructed actual original relation map on the whole retained old kernel. -/
def oldEnvelopeKernelLift : (b ⁻¹ᵁ W).toScheme ⟶ (relation f hL d V c k).left :=
  (K).homOfLE (oldEnvelopeTarget_kernel_le_inverse f hL d V c k) ≫
    MonomorphismOpenImage.lift m

/-- The original relation map is a section of the unchanged old kernel map. -/
@[reassoc]
theorem oldEnvelopeKernelLift_comp :
    oldEnvelopeKernelLift f hL d V c k ≫ m = (b ⁻¹ᵁ W).ι := by
  rw [oldEnvelopeKernelLift, Category.assoc, MonomorphismOpenImage.lift_comp,
    Scheme.homOfLE_ι]

/-- Arbitrary tests, including nonreduced ones, have unique original relation arrows. -/
theorem oldEnvelopeTarget_original_test {Z : Scheme} (a a' : Z ⟶ A.left)
    (ha : a ≫ v = a' ≫ v) (hW : Set.range (a ≫ v) ⊆ W) :
    ∃! z : Z ⟶ (relation f hL d V c k).left, z ≫ p = a ∧ z ≫ q = a' := by
  let t := pullback.lift a a' ha
  have ht : Set.range (t ≫ b) ⊆ KernelPairEffectiveOpen.targetOpen p q v h := by
    rw [← Category.assoc, pullback.lift_fst]
    exact hW.trans (oldEnvelopeTarget_le_effective f hL d V c k)
  obtain ⟨z, hz, hu⟩ := MonomorphismRelativeOpen.test_lift m b t ht
  refine ⟨z, ⟨?_, ?_⟩, ?_⟩
  · simpa only [Category.assoc, pullback.lift_fst, t] using
      congrArg (fun g ↦ g ≫ pullback.fst v v) hz
  · simpa only [Category.assoc, pullback.lift_snd, t] using
      congrArg (fun g ↦ g ≫ pullback.snd v v) hz
  · intro z' hz'
    apply hu z'
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst, t] using hz'.1
    · simpa only [Category.assoc, pullback.lift_snd, t] using hz'.2

end FLT.Mazur.HilbertChart.AffineRestriction
