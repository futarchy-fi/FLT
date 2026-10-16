/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupOrbitSpan

/-!
# Separating the identity in a free finite orbit

The fixed-point ideal of each nonidentity element gives a separating orbit
combination. Multiplying these finitely many combinations constructs the
identity delta function in the span of original orbit profiles. This retains
scheme-theoretic freeness, including over rings of positive characteristic.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace FLT.Mazur.FiniteGroupQuotient
variable (G : Type*) [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]

/-- Equations of the fixed subscheme of a group element. -/
def fixedPointIdeal (g : G) : Ideal A :=
  Ideal.span (Set.range (fun a : A ↦ a - g • a))

/-- Values at the identity of orbit combinations vanishing at the specified element. -/
def separationValues (g : G) : Ideal A where
  carrier := {a | ∃ v ∈ orbitSpan G A, v 1 = a ∧ v g = 0}
  zero_mem' := ⟨0, (orbitSpan G A).zero_mem, rfl, rfl⟩
  add_mem' := by
    rintro a b ⟨v, hv, hv₁, hvg⟩ ⟨w, hw, hw₁, hwg⟩
    exact ⟨v + w, (orbitSpan G A).add_mem hv hw, by simp [hv₁, hw₁],
      by simp [hvg, hwg]⟩
  smul_mem' := by
    rintro a b ⟨v, hv, hv₁, hvg⟩
    exact ⟨a • v, (orbitSpan G A).smul_mem a hv, by simp [hv₁], by simp [hvg]⟩

/-- Every fixed-point equation is the identity value of a vanishing orbit combination. -/
theorem fixedPointIdeal_le_separationValues (g : G) :
    fixedPointIdeal G A g ≤ separationValues G A g := by
  apply Ideal.span_le.mpr
  rintro _ ⟨a, rfl⟩
  refine ⟨orbitProfile G A a - (fun _ ↦ g • a),
    (orbitSpan G A).sub_mem (orbitProfile_mem G A a)
      (constant_mem_orbitSpan G A (g • a)), ?_, ?_⟩
  · simp only [Pi.sub_apply, orbitProfile, one_smul]
  · exact sub_self (g • a)

/-- An empty fixed subscheme constructs a separator, without division by its orbit size. -/
theorem exists_orbit_separator (g : G) (hg : fixedPointIdeal G A g = ⊤) :
    ∃ v ∈ orbitSpan G A, v 1 = 1 ∧ v g = 0 := by
  apply fixedPointIdeal_le_separationValues G A g
  rw [hg]
  trivial

variable [Finite G]

/-- Freeness constructs the identity delta as a finite combination of actual orbit profiles. -/
theorem exists_identity_orbit_combination
    (hfree : ∀ g : G, g ≠ 1 → fixedPointIdeal G A g = ⊤) :
    ∃ v ∈ orbitSpan G A, v 1 = 1 ∧ ∀ g : G, g ≠ 1 → v g = 0 := by
  classical
  let _ := Fintype.ofFinite G
  choose v hv hv₁ hv₀ using fun g : {g : G // g ≠ 1} ↦
    exists_orbit_separator G A g.val (hfree g.val g.property)
  refine ⟨∏ g, v g, orbitSpan_prod G A Finset.univ v (fun g _ ↦ hv g), ?_, ?_⟩
  · simp only [Finset.prod_apply, hv₁, Finset.prod_const_one]
  · intro g hg
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨g, hg⟩ : {g : G // g ≠ 1}))
      (hv₀ ⟨g, hg⟩)

end FLT.Mazur.FiniteGroupQuotient
