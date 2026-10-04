/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Monoid

/-!
# A fixed integral lift of a residual quadratic character

A square-one field-valued character takes values in {1,-1}. Its sign gives a
specified lift to every coefficient ring, compatible with reduction and change
of coefficients. A subgroup acting trivially residually acts trivially in the
lift, so this construction preserves unramifiedness.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation

variable {G k : Type*} [Group G] [Field k]
  (χ : G →* kˣ) (hχ : ∀ g, χ g ^ 2 = 1)

include hχ in
/-- Values of the actual residual quadratic character are signs. -/
theorem quadraticCharacter_sign (g : G) : χ g = 1 ∨ χ g = -1 := by
  have h : (χ g : k) ^ 2 = 1 := congrArg Units.val (hχ g)
  rcases sq_eq_one_iff.mp h with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext h)

variable (A : Type*) [CommRing A]

/-- The specified sign lift; no character lift is supplied as a hypothesis. -/
def quadraticCharacterLift : G →* Aˣ := by
  classical
  exact
    { toFun := fun g ↦ if χ g = 1 then 1 else -1
      map_one' := by simp
      map_mul' := by
        intro g h
        by_cases hg : χ g = 1 <;> by_cases hh : χ h = 1
        · simp [map_mul, hg, hh]
        · simp [map_mul, hg, hh]
        · simp [map_mul, hg, hh]
        · have hg' := (quadraticCharacter_sign χ hχ g).resolve_left hg
          have hh' := (quadraticCharacter_sign χ hχ h).resolve_left hh
          have hgh : χ (g * h) = 1 := by rw [map_mul, hg', hh']; simp
          simp [hgh, hg, hh] }

/-- The lift is quadratic over the integral coefficient ring. -/
theorem quadraticCharacterLift_sq (g : G) : quadraticCharacterLift χ hχ A g ^ 2 = 1 := by
  classical
  change (if χ g = 1 then (1 : Aˣ) else -1) ^ 2 = 1
  split <;> simp

/-- Reducing the fixed integral lift recovers the original residual character. -/
theorem quadraticCharacterLift_reduce (r : A →+* k) (g : G) :
    Units.map r.toMonoidHom (quadraticCharacterLift χ hχ A g) = χ g := by
  classical
  by_cases hg : χ g = 1
  · simp [quadraticCharacterLift, hg]
  · have hg' := (quadraticCharacter_sign χ hχ g).resolve_left hg
    apply Units.ext
    change r (↑(if χ g = 1 then (1 : Aˣ) else -1)) = (χ g : k)
    rw [ite_eq_right hg, hg']
    simp

/-- The same sign lift is used after every change of coefficient rings. -/
theorem quadraticCharacterLift_map {D : Type*} [CommRing D] (r : A →+* D) (g : G) :
    Units.map r.toMonoidHom (quadraticCharacterLift χ hχ A g) =
      quadraticCharacterLift χ hχ D g := by
  classical
  apply Units.ext
  by_cases hg : χ g = 1 <;> simp [quadraticCharacterLift, hg]

/-- Any subgroup killed by the residual character is killed by the fixed lift. -/
theorem quadraticCharacterLift_trivial_on (N : Subgroup G)
    (hN : ∀ g ∈ N, χ g = 1) (g : G) (hg : g ∈ N) :
    quadraticCharacterLift χ hχ A g = 1 := by
  classical
  simp [quadraticCharacterLift, hN g hg]

/-- Continuous residual characters with discrete coefficients give continuous lifts. -/
theorem quadraticCharacterLift_continuous [TopologicalSpace G] [TopologicalSpace k]
    [DiscreteTopology k] [TopologicalSpace A] (hc : Continuous χ) :
    Continuous (quadraticCharacterLift χ hχ A) := by
  classical
  exact (continuous_of_discreteTopology
    (f := fun u : kˣ ↦ if u = 1 then (1 : Aˣ) else -1)).comp hc

end GaloisRepresentation
