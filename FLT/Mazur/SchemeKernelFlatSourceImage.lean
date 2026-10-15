/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFlatSourceImage
public import FLT.Mazur.KernelPairEffectiveOpen
public import FLT.Mazur.SchemeKernelInvariantOpenLift

/-!
# Effective target neighborhoods from saturated source inverse opens

An actual inverse on a saturated source open extends to the entire kernel
over its constructed flat image. The image lies in both the effective target
and its original fppf region. All statements retain the old target scheme,
not just reduced points or a newly chosen coefficient model.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeKernelFlatSourceImage
set_option backward.isDefEq.respectTransparency false
variable {D A T : Scheme.{u}} (p q : D ⟶ A) (w : A ⟶ T) (h : p ≫ w = q ≫ w)
  [LocallyOfFinitePresentation w] (U : A.Opens)
  (hsat : ∀ x y : A, w x = w y → (x ∈ U ↔ y ∈ U))
local notation "m" => pullback.lift p q h
local notation "W" => SchemeFlatSourceImage.image w U
local notation "K" => (pullback w w : Scheme)
local notation "b" => pullback.fst w w ≫ w

include hsat in
/-- The entire kernel over the flat image lies above the original saturated source open. -/
theorem kernel_preimage_le :
    b ⁻¹ᵁ W ≤ SchemeKernelInvariantOpenLift.openDomain w U := by
  intro z hz
  exact SchemeFlatSourceImage.preimage_le w U hsat hz

include hsat in
/-- Source inverse neighborhoods construct effective neighborhoods in the unchanged target. -/
theorem image_le_effective
    (hi : SchemeKernelInvariantOpenLift.openDomain w U ≤ MonomorphismOpenImage.locus m) :
    W ≤ KernelPairEffectiveOpen.targetOpen p q w h :=
  SchemeWholeFiberOpen.le_locus b (MonomorphismOpenImage.locus m) W
    ((kernel_preimage_le w U hsat).trans hi)

variable [Mono (pullback.lift p q h)]

/-- An actual original arrow on the complete old kernel over the constructed flat image. -/
def originalLift
    (hi : SchemeKernelInvariantOpenLift.openDomain w U ≤ MonomorphismOpenImage.locus m) :
    (b ⁻¹ᵁ W).toScheme ⟶ D :=
  (K).homOfLE ((kernel_preimage_le w U hsat).trans hi) ≫ MonomorphismOpenImage.lift m

/-- The constructed inverse retains the literal inclusion into the old scheme kernel. -/
@[reassoc]
theorem originalLift_comp
    (hi : SchemeKernelInvariantOpenLift.openDomain w U ≤ MonomorphismOpenImage.locus m) :
    originalLift p q w h U hsat hi ≫ m = (b ⁻¹ᵁ W).ι := by
  rw [originalLift, Category.assoc, MonomorphismOpenImage.lift_comp, Scheme.homOfLE_ι]

include hsat in
/-- Every scheme test over the retained target has a unique full original relation arrow. -/
theorem original_test_lift
    (hi : SchemeKernelInvariantOpenLift.openDomain w U ≤ MonomorphismOpenImage.locus m)
    {Z : Scheme.{u}} (a b' : Z ⟶ A) (hab : a ≫ w = b' ≫ w)
    (ha : Set.range (a ≫ w) ⊆ W) :
    ∃! z : Z ⟶ D, z ≫ p = a ∧ z ≫ q = b' := by
  let t := pullback.lift a b' hab
  have ht : Set.range (t ≫ b) ⊆ KernelPairEffectiveOpen.targetOpen p q w h := by
    rw [← Category.assoc, pullback.lift_fst]
    exact ha.trans (image_le_effective p q w h U hsat hi)
  obtain ⟨z, hz, hu⟩ := MonomorphismRelativeOpen.test_lift m b t ht
  refine ⟨z, ⟨?_, ?_⟩, ?_⟩
  · simpa only [Category.assoc, pullback.lift_fst, t] using
      congrArg (fun g ↦ g ≫ pullback.fst w w) hz
  · simpa only [Category.assoc, pullback.lift_snd, t] using
      congrArg (fun g ↦ g ≫ pullback.snd w w) hz
  · intro z' hz'
    apply hu z'
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst, t] using hz'.1
    · simpa only [Category.assoc, pullback.lift_snd, t] using hz'.2

end FLT.Mazur.SchemeKernelFlatSourceImage
