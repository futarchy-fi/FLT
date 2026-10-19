/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicPrincipalRestriction

/-!
# Power torsion on invariant principal neighborhoods

The Noetherian original source detects vanishing of invariant functions by a
finite power of the defining function. The proved compactness of every full
relation domain gives the corresponding test for relation equations.
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

/-- Vanishing on a principal neighborhood is equivalent to finite-power annihilation. -/
theorem principalRestriction_eq_zero_iff
    (x : (invariantSheaf n).obj.obj (op W)) :
    principalRestriction n W s x = 0 ↔ ∃ k : ℕ, s ^ k * x = 0 := by
  constructor
  · intro hx
    let _ := (principalSourceRestriction n W s).toAlgebra
    let _ := principalSourceRestriction_isLocalization n W s
    have hz : principalSourceRestriction n W s
        ((invariantInclusion n).hom.app (op W) x) =
        principalSourceRestriction n W s 0 := by
      rw [← principalRestriction_inclusion, hx, map_zero, map_zero]
    obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq ((invariantInclusion n).hom.app (op W) s) hz
    refine ⟨k, invariantSection_ext n W ?_⟩
    simpa only [map_mul, map_pow, map_zero, mul_zero] using hk
  · rintro ⟨k, hk⟩
    have he := congrArg (principalRestriction n W s) hk
    rw [map_mul, map_pow, map_zero] at he
    exact (IsUnit.mul_right_eq_zero ((principalRestriction_isUnit n W s).pow k)).mp he

/-- Restriction of all functions on the full original relation. -/
def principalRelationRestriction : (relationSheaf n).obj.obj (op W) →+*
    (relationSheaf n).obj.obj (op D) :=
  ((relationSheaf n).obj.map (j).op).hom

/-- The relation domain is the basic open of the first pullback of the invariant function. -/
theorem principalRelationOpen :
    (src) ⁻¹ᵁ (pullOpen n D).val =
      (A).basicOpen
        ((firstRestriction n).hom.app (op W) ((invariantInclusion n).hom.app (op W) s)) := by
  rw [pullOpen_invariantPrincipal]
  exact Scheme.preimage_basicOpen (src) ((invariantInclusion n).hom.app (op W) s)

/-- Compactness clears a relation equation that vanishes on the principal neighborhood. -/
theorem principalRelationRestriction_pow
    (x : (relationSheaf n).obj.obj (op W))
    (hx : principalRelationRestriction n W s x = 0) :
    ∃ k : ℕ,
      ((firstRestriction n).hom.app (op W)
        ((invariantInclusion n).hom.app (op W) s)) ^ k * x = 0 := by
  suffices h : ∀ (V : (A).Opens) (i : V ⟶ (src) ⁻¹ᵁ (pullOpen n W).val),
      V = (A).basicOpen
        ((firstRestriction n).hom.app (op W) ((invariantInclusion n).hom.app (op W) s)) →
      (A).presheaf.map i.op x = 0 →
      ∃ k : ℕ,
      ((firstRestriction n).hom.app (op W)
        ((invariantInclusion n).hom.app (op W) s)) ^ k * x = 0 from
    h _ _ (principalRelationOpen n W s) hx
  intro V i hV hx
  subst V
  exact exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact (A)
    (disjointComparisonSource_preimage_isCompact n (pullOpen n W).val) x _ hx

end FLT.Mazur.CyclicCharacteristicOrbit
