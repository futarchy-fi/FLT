/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassSmoothLocalRootLift
public import FLT.Mazur.AdicFormallySmoothStages

/-!
# Actual adic reductions of smooth Weierstrass points

The successive positive-power quotient maps have square-zero kernels. Over a
local coefficient ring they lift smooth-group points and uniquely lift every
unit-index power root, with the original complete-section reductions retained.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.WeierstrassSmoothAdicReduction

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open WeierstrassIntegralChart

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (I : Ideal R)

/-- Smooth-group points over the actual positive-order coefficient quotient. -/
abbrev Points (m : ℕ) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (m + 1))))) ⟶
    (integralSmoothGroup W).X

/-- Actual restriction of smooth-group points between successive adic stages. -/
def reduction (m : ℕ) : Points W I (m + 1) →* Points W I m :=
  smoothAlgebraReduction W (AdicFormallySmoothStages.restriction I m)

/-- Restriction of an original full-base section to the specified adic order. -/
def sectionReduction (m : ℕ) :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R R))) ⟶
      (integralSmoothGroup W).X) →* Points W I m :=
  smoothAlgebraReduction W (Ideal.Quotient.mkₐ R (I ^ (m + 1)))

/-- Adjacent reductions of a full-base section agree as complete relative scheme maps. -/
theorem reduction_sectionReduction (m : ℕ)
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R R))) ⟶
      (integralSmoothGroup W).X) :
    reduction W I m (sectionReduction W I (m + 1) x) = sectionReduction W I m x := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom
      (AdicFormallySmoothStages.restriction I m).toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (m + 2)))) ≫ x.left) = _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

variable [IsLocalRing R] (hI : I ≠ ⊤)

include hI in
/-- Each positive adic quotient is still a local ring. -/
theorem stage_isLocalRing (m : ℕ) : IsLocalRing (R ⧸ I ^ (m + 1)) := by
  have hp : I ^ (m + 1) ≠ ⊤ := by
    intro he
    exact (Ideal.pow_eq_top_iff.mp he).elim hI (Nat.succ_ne_zero m)
  let _ : Nontrivial (R ⧸ I ^ (m + 1)) := Ideal.Quotient.nontrivial_iff.mpr hp
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

include hI in
/-- Every root of the reduced original point lifts uniquely to the next actual adic order. -/
theorem existsUnique_next_root (n : ℕ) (hn : IsUnit (n : R)) (m : ℕ)
    (x : Points W I (m + 1)) (b : Points W I m) (hb : b ^ n = reduction W I m x) :
    ∃! y : Points W I (m + 1), reduction W I m y = b ∧ y ^ n = x := by
  let _ := stage_isLocalRing I hI m
  have hu : IsUnit (n : R ⧸ I ^ (m + 2)) := by
    simpa only [map_natCast] using hn.map (algebraMap R (R ⧸ I ^ (m + 2)))
  exact smoothLocal_existsUnique_power_lift W (AdicFormallySmoothStages.restriction I m)
    (AdicFormallySmoothStages.restriction_surjective I m)
    (AdicFormallySmoothStages.restriction_kernel_square I m) n hu x b hb

end FLT.Mazur.WeierstrassSmoothAdicReduction
