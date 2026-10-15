/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationPrincipalTorsion
public import FLT.Mazur.EqualizerDenominatorClearing

/-!
# Localization of the full invariant structure sheaf

On an affine source domain with compact full relation domain, every invariant
section on a principal neighborhood has an invariant numerator. The actual
invariant section ring is therefore the localization of the original invariant
ring. No affine chart on the orbit space is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (W : Opens (Orbit e))
  (s : (invariantSheaf e).obj.obj (op W))
  (hW : IsAffineOpen (pullOpen e W).val)
  (hR : IsCompact (p.left ⁻¹ᵁ (pullOpen e W).val : Set A.left))
local notation "D" => invariantPrincipal e W s
local notation "j" => homOfLE (invariantPrincipal_le e W s)
include hW hR

/-- Every local invariant section has an actual invariant numerator after a finite power. -/
theorem principalRestriction_invariant_numerator
    (b : (invariantSheaf e).obj.obj (op D)) :
    ∃ (N : ℕ) (y : (invariantSheaf e).obj.obj (op W)),
      b * principalRestriction e W s s ^ N = principalRestriction e W s y := by
  obtain ⟨N, y, hy, he⟩ := EqualizerDenominatorClearing.exists_invariant_numerator
    ((firstRestriction e).hom.app (op W)).hom
    ((secondRestriction e).hom.app (op W)).hom
    (principalSourceRestriction e W s) (principalRelationRestriction e W s)
    ((firstRestriction e).hom.app (op D)).hom
    ((secondRestriction e).hom.app (op D)).hom
    (fun x ↦ congrArg (fun k ↦ k x) ((firstRestriction e).hom.naturality (j).op))
    (fun x ↦ congrArg (fun k ↦ k x) ((secondRestriction e).hom.naturality (j).op))
    ((invariantInclusion e).hom.app (op W) s) (invariantSection_condition e W s)
    (principalRelationRestriction_pow e W s hR)
    (principalSourceRestriction_isLocalization e W s hW)
    ((invariantInclusion e).hom.app (op D) b) (invariantSection_condition e D b)
  obtain ⟨t, ht, _⟩ := invariantSection_existsUnique e W y hy
  refine ⟨N, t, invariantSection_ext e D ?_⟩
  rw [map_mul, map_pow, principalRestriction_inclusion, principalRestriction_inclusion, ht]
  exact he

/-- Principal restriction of the actual invariant sheaf is localization, including torsion. -/
theorem principalRestriction_isLocalization :
    @IsLocalization.Away _ _ s ((invariantSheaf e).obj.obj (op D)) _
      (principalRestriction e W s).toAlgebra := by
  let _ := (principalRestriction e W s).toAlgebra
  apply IsLocalization.Away.mk s
  · exact principalRestriction_isUnit e W s
  · exact principalRestriction_invariant_numerator e W s hW hR
  · intro a b hab
    change principalRestriction e W s a = principalRestriction e W s b at hab
    have hz : principalRestriction e W s (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    obtain ⟨n, hn⟩ := (principalRestriction_eq_zero_iff e W s hW (a - b)).mp hz
    exact ⟨n, sub_eq_zero.mp (by simpa only [mul_sub] using hn)⟩

end FLT.Mazur.RelativeRelationOrbit
