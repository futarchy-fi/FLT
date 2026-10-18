/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassSmoothSurjectiveKernel
public import FLT.Mazur.SmoothLocalNilpotentLift
public import FLT.Mazur.KernelPowerRootLifting

/-!
# Actual smooth-group power-root lifting across local square-zero extensions

Smoothness constructs a lift of the prescribed reduced root. The square-zero
kernel calculation corrects its power and proves uniqueness, keeping the
original coefficient restriction and the specified target point.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [IsLocalRing B]
  (W : WeierstrassCurve R) (φ : A →ₐ[R] B)
  (hφ : Function.Surjective φ) (hker : IsNilpotent (RingHom.ker φ.toRingHom))

include hφ hker in
/-- Actual smooth-group points lift across every local nilpotent coefficient surjection. -/
theorem smoothAlgebraReduction_surjective : Function.Surjective (smoothAlgebraReduction W φ) := by
  intro p
  obtain ⟨s, hs, hf⟩ := SmoothLocalNilpotentLift.exists_lift (integralSmoothStructure W)
    φ hφ hker p.left p.w
  exact ⟨Over.homMk s hf, Over.OverMorphism.ext hs⟩

include hφ in
/-- Every prescribed reduced power root has a unique lift across a square-zero extension. -/
theorem smoothLocal_existsUnique_power_lift (hsq : RingHom.ker φ.toRingHom ^ 2 = ⊥)
    (n : ℕ) (hn : IsUnit (n : A))
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      (integralSmoothGroup W).X)
    (b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶
      (integralSmoothGroup W).X)
    (hb : b ^ n = smoothAlgebraReduction W φ x) :
    ∃! y, smoothAlgebraReduction W φ y = b ∧ y ^ n = x :=
  KernelPowerTorsionLifting.existsUnique_power_lift (smoothAlgebraReduction W φ) n
    (smoothAlgebraReduction_surjective W φ hφ ⟨2, hsq⟩)
    (smoothAlgebraReduction_kernel_pow_bijective W φ hφ hsq n hn) x b hb

end FLT.Mazur.WeierstrassIntegralChart
