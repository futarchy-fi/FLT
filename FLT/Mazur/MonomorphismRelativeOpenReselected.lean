/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonomorphismRelativeOpenTransport

/-!
# Effective regions retained from the original inverse locus

First pull the original relation's inverse locus into the reselected kernel,
then keep whole new fibers. This retains at least the inverse image of the
old effective target open. Old bad pairs absent from the new kernel need not
exclude a new target neighborhood. No strict enlargement or coverage is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.MonomorphismRelativeOpen
variable {D K T D' K' T' : Scheme.{u}} (m : D ⟶ K)
  (b : K' ⟶ K) (q' : K' ⟶ T')

/-- Remove only old bad relation pairs that actually occur in the new kernel. -/
def retainedTargetOpen : T'.Opens :=
  SchemeWholeFiberOpen.locus q' (b ⁻¹ᵁ MonomorphismOpenImage.locus m)

/-- Every retained new kernel test maps into the actual old inverse locus. -/
theorem retainedTargetOpen_preimage_le :
    q' ⁻¹ᵁ retainedTargetOpen m b q' ≤ b ⁻¹ᵁ MonomorphismOpenImage.locus m :=
  SchemeWholeFiberOpen.preimage_le q' _

/-- This construction retains at least every effective old target neighborhood. -/
theorem preimage_targetOpen_le_retained (q : K ⟶ T) (t : T' ⟶ T)
    (hK : b ≫ q = q' ≫ t) :
    t ⁻¹ᵁ targetOpen m q ≤ retainedTargetOpen m b q' := by
  apply SchemeWholeFiberOpen.le_locus
  intro x hx
  apply SchemeWholeFiberOpen.preimage_le q (MonomorphismOpenImage.locus m)
  change q (b x) ∈ targetOpen m q
  rw [show q (b x) = t (q' x) from congrArg (fun z ↦ z x) hK]
  exact hx

variable [Mono m] (a : D' ⟶ D) (m' : D' ⟶ K') (hD : IsPullback a m' m b)

include hD in
/-- The full relation pullback proves that every retained new fiber is effective. -/
theorem retainedTargetOpen_le : retainedTargetOpen m b q' ≤ targetOpen m' q' :=
  SchemeWholeFiberOpen.monotone q'
    (MonomorphismOpenImage.preimage_locus_le m a m' b hD)

include hD in
/-- Every scheme test over this retained region has a unique original new relation arrow. -/
theorem retainedTargetOpen_test_lift {Z : Scheme.{u}} (x : Z ⟶ K')
    (hx : Set.range (x ≫ q') ⊆ retainedTargetOpen m b q') :
    ∃! z : Z ⟶ D', z ≫ m' = x := by
  let _ : Mono m' := hD.mono_snd_of_mono
  exact test_lift m' q' x (hx.trans (retainedTargetOpen_le m b q' a m' hD))

end FLT.Mazur.MonomorphismRelativeOpen
