/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicPrincipalTorsion
public import FLT.Mazur.EqualizerDenominatorClearing

/-!
# Localization of the full invariant structure sheaf

On every orbit open, a section on an invariant principal neighborhood has an
invariant numerator, using the proved Noetherian source and relation. The actual
invariant section ring is therefore the localization of the original invariant
ring. No affine chart on the orbit space is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]
local notation "U" => normalizedDisjointSource n
local notation "A" => disjointComparisonArrows n
local notation "src" => disjointComparisonSource n
variable (W : Opens (Orbit n))
  (s : (invariantSheaf n).obj.obj (op W))
local notation "D" => invariantPrincipal n W s
local notation "j" => homOfLE (invariantPrincipal_le n W s)

/-- Every local invariant section has an actual invariant numerator after a finite power. -/
theorem principalRestriction_invariant_numerator
    (b : (invariantSheaf n).obj.obj (op D)) :
    ∃ (N : ℕ) (y : (invariantSheaf n).obj.obj (op W)),
      b * principalRestriction n W s s ^ N = principalRestriction n W s y := by
  obtain ⟨N, y, hy, he⟩ := EqualizerDenominatorClearing.exists_invariant_numerator
    ((firstRestriction n).hom.app (op W)).hom
    ((secondRestriction n).hom.app (op W)).hom
    (principalSourceRestriction n W s) (principalRelationRestriction n W s)
    ((firstRestriction n).hom.app (op D)).hom
    ((secondRestriction n).hom.app (op D)).hom
    (fun x ↦ congrArg (fun k ↦ k x) ((firstRestriction n).hom.naturality (j).op))
    (fun x ↦ congrArg (fun k ↦ k x) ((secondRestriction n).hom.naturality (j).op))
    ((invariantInclusion n).hom.app (op W) s) (invariantSection_condition n W s)
    (principalRelationRestriction_pow n W s)
    (principalSourceRestriction_isLocalization n W s)
    ((invariantInclusion n).hom.app (op D) b) (invariantSection_condition n D b)
  obtain ⟨t, ht, _⟩ := invariantSection_existsUnique n W y hy
  refine ⟨N, t, invariantSection_ext n D ?_⟩
  rw [map_mul, map_pow, principalRestriction_inclusion, principalRestriction_inclusion, ht]
  exact he

/-- Principal restriction of the actual invariant sheaf is localization, including torsion. -/
theorem principalRestriction_isLocalization :
    @IsLocalization.Away _ _ s ((invariantSheaf n).obj.obj (op D)) _
      (principalRestriction n W s).toAlgebra := by
  let _ := (principalRestriction n W s).toAlgebra
  apply IsLocalization.Away.mk s
  · exact principalRestriction_isUnit n W s
  · exact principalRestriction_invariant_numerator n W s
  · intro a b hab
    change principalRestriction n W s a = principalRestriction n W s b at hab
    have hz : principalRestriction n W s (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    obtain ⟨k, hk⟩ := (principalRestriction_eq_zero_iff n W s (a - b)).mp hz
    exact ⟨k, sub_eq_zero.mp (by simpa only [mul_sub] using hk)⟩

end FLT.Mazur.CyclicCharacteristicOrbit
