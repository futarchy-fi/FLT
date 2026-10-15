/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationPrincipalRestriction

/-!
# Power torsion on invariant principal neighborhoods

Affine source domains detect vanishing of invariant functions by a finite
power of the defining function. Compactness of the full relation domain gives
the corresponding finite-power test for relation equations.
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
local notation "D" => invariantPrincipal e W s
local notation "j" => homOfLE (invariantPrincipal_le e W s)

/-- Vanishing on a principal neighborhood is equivalent to finite-power annihilation. -/
theorem principalRestriction_eq_zero_iff (hW : IsAffineOpen (pullOpen e W).val)
    (x : (invariantSheaf e).obj.obj (op W)) :
    principalRestriction e W s x = 0 ↔ ∃ n : ℕ, s ^ n * x = 0 := by
  constructor
  · intro hx
    let _ := (principalSourceRestriction e W s).toAlgebra
    let _ := principalSourceRestriction_isLocalization e W s hW
    have hz : principalSourceRestriction e W s
        ((invariantInclusion e).hom.app (op W) x) =
        principalSourceRestriction e W s 0 := by
      rw [← principalRestriction_inclusion, hx, map_zero, map_zero]
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq ((invariantInclusion e).hom.app (op W) s) hz
    refine ⟨n, invariantSection_ext e W ?_⟩
    simpa only [map_mul, map_pow, map_zero, mul_zero] using hn
  · rintro ⟨n, hn⟩
    have he := congrArg (principalRestriction e W s) hn
    rw [map_mul, map_pow, map_zero] at he
    exact (IsUnit.mul_right_eq_zero ((principalRestriction_isUnit e W s).pow n)).mp he

/-- Restriction of all functions on the full original relation. -/
def principalRelationRestriction : (relationSheaf e).obj.obj (op W) →+*
    (relationSheaf e).obj.obj (op D) :=
  ((relationSheaf e).obj.map (j).op).hom

/-- The relation domain is the basic open of the first pullback of the invariant function. -/
theorem principalRelationOpen :
    p.left ⁻¹ᵁ (pullOpen e D).val =
      A.left.basicOpen
        ((firstRestriction e).hom.app (op W) ((invariantInclusion e).hom.app (op W) s)) := by
  rw [pullOpen_invariantPrincipal]
  exact Scheme.preimage_basicOpen p.left ((invariantInclusion e).hom.app (op W) s)

/-- Compactness clears a relation equation that vanishes on the principal neighborhood. -/
theorem principalRelationRestriction_pow
    (hW : IsCompact (p.left ⁻¹ᵁ (pullOpen e W).val : Set A.left))
    (x : (relationSheaf e).obj.obj (op W))
    (hx : principalRelationRestriction e W s x = 0) :
    ∃ n : ℕ,
      ((firstRestriction e).hom.app (op W)
        ((invariantInclusion e).hom.app (op W) s)) ^ n * x = 0 := by
  suffices h : ∀ (V : A.left.Opens) (i : V ⟶ p.left ⁻¹ᵁ (pullOpen e W).val),
      V = A.left.basicOpen
        ((firstRestriction e).hom.app (op W) ((invariantInclusion e).hom.app (op W) s)) →
      A.left.presheaf.map i.op x = 0 →
      ∃ n : ℕ,
      ((firstRestriction e).hom.app (op W)
        ((invariantInclusion e).hom.app (op W) s)) ^ n * x = 0 from
    h _ _ (principalRelationOpen e W s) hx
  intro V i hV hx
  subst V
  exact exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact A.left hW x _ hx

end FLT.Mazur.RelativeRelationOrbit
