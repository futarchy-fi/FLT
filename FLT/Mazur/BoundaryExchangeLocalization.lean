/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryExchangeObstruction
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Localizing the exact exchange obstruction

Vanishing after localization gives a denominator and an actual target
boundary-kernel correction. Equivalently, a denominator multiple of the boundary
value has an exchange-free lift. No annihilator or vanishing is assumed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.BoundaryExchangeObstruction
variable {R T B S : Type*} [CommRing R]
  [AddCommGroup T] [AddCommGroup B] [AddCommGroup S]
  [Module R T] [Module R B] [Module R S]
  (b : T →ₗ[R] B) (δ : T →ₗ[R] S) (M : Submonoid R)

/-- The exact exchange class localized at a specified original multiplicative set. -/
def localizedLiftClass : T →ₗ[R] LocalizedModule M (S ⧸ correctionImage b δ) :=
  (LocalizedModule.mkLinearMap M _).comp (liftClass b δ)

/-- Local vanishing means an actual denominator multiple lies in the correction image. -/
theorem localizedLiftClass_zero_iff (v : T) :
    localizedLiftClass b δ M v = 0 ↔
      ∃ s : M, ∃ z : T, b z = 0 ∧ δ z = (s : R) • δ v := by
  change (LocalizedModule.mkLinearMap M _) (liftClass b δ v) = 0 ↔ _
  rw [IsLocalizedModule.eq_zero_iff M]
  constructor
  · rintro ⟨s, hs⟩
    have h : liftClass b δ ((s : R) • v) = 0 := by
      simpa only [map_smul, Submonoid.smul_def] using hs
    obtain ⟨z, hz, hd⟩ := (liftClass_zero_iff b δ _).mp h
    exact ⟨s, z, hz, by simpa only [map_smul] using hd⟩
  · rintro ⟨s, z, hz, hd⟩
    refine ⟨s, ?_⟩
    have h := (liftClass_zero_iff b δ ((s : R) • v)).mpr
      ⟨z, hz, by simpa only [map_smul] using hd⟩
    simpa only [map_smul, Submonoid.smul_def] using h

/-- Clearing a denominator constructs an exchange-free lift of the scaled boundary value. -/
theorem localizedLiftClass_zero_iff_lift (v : T) :
    localizedLiftClass b δ M v = 0 ↔
      ∃ s : M, ∃ w : T, b w = (s : R) • b v ∧ δ w = 0 := by
  rw [localizedLiftClass_zero_iff]
  constructor
  · rintro ⟨s, z, hz, hd⟩
    refine ⟨s, (s : R) • v - z, ?_, ?_⟩
    · rw [map_sub, map_smul, hz, sub_zero]
    · rw [map_sub, map_smul, hd, sub_self]
  · rintro ⟨s, w, hw, hd⟩
    refine ⟨s, (s : R) • v - w, ?_, ?_⟩
    · rw [map_sub, map_smul, hw, sub_self]
    · rw [map_sub, map_smul, hd, sub_zero]

/-- Exact lifts of the same boundary value still have equal localized obstructions. -/
theorem localizedLiftClass_independent (v w : T) (h : b v = b w) :
    localizedLiftClass b δ M v = localizedLiftClass b δ M w :=
  congrArg (LocalizedModule.mkLinearMap M _) (liftClass_eq_of_boundary_eq b δ v w h)

end FLT.Mazur.BoundaryExchangeObstruction
