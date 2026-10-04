/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Divided-power closure inside a fixed ambient ring

Intersect the subrings containing a given base and closed under ambient
divided powers. The intersection has an actual divided-power ideal and is
minimal among such subrings. This is an embedded hull construction, not an
abstract universal divided-power envelope.
-/

@[expose] public noncomputable section
namespace DividedPowers
variable {B : Type*} [CommRing B] {J : Ideal B} (hJ : DividedPowers J) (T : Subring B)

/-- The least subring containing the base and closed under the ambient divided powers. -/
def hull : Subring B := sInf {S : Subring B | T ≤ S ∧
  ∀ (n : ℕ) (x : B), x ∈ S → x ∈ J → hJ.dpow n x ∈ S}

/-- The base ring lies in its divided-power hull. -/
theorem le_hull : T ≤ hJ.hull T := le_sInf fun _ h ↦ h.1

/-- Minimality inside the fixed ambient divided-power ring. -/
theorem hull_le {S : Subring B} (hT : T ≤ S)
    (hS : ∀ (n : ℕ) (x : B), x ∈ S → x ∈ J → hJ.dpow n x ∈ S) :
    hJ.hull T ≤ S := sInf_le ⟨hT, hS⟩

/-- Closure under the ambient operations follows from intersection, without extra hypotheses. -/
theorem dpow_mem_hull (n : ℕ) {x : B} (hx : x ∈ hJ.hull T) :
    hJ.dpow n x ∈ hJ.hull T := by
  by_cases h : x ∈ J
  · rw [hull, Subring.mem_sInf]
    intro S hS
    exact hS.2 n x ((sInf_le hS : hJ.hull T ≤ S) hx) h
  · rw [hJ.dpow_null h]
    exact (hJ.hull T).zero_mem

/-- The induced divided-power ideal is the intersection with the ambient ideal. -/
def hullIdeal : Ideal (hJ.hull T) := J.comap (hJ.hull T).subtype

/-- Ambient divided powers, now valued in the constructed hull. -/
def hullDpow (n : ℕ) (x : hJ.hull T) : hJ.hull T :=
  ⟨hJ.dpow n x, hJ.dpow_mem_hull T n x.property⟩

/-- The hull carries genuine divided powers on the induced ideal. -/
def hullDividedPowers : DividedPowers (hJ.hullIdeal T) where
  dpow := hJ.hullDpow T
  dpow_null hx := Subtype.ext (hJ.dpow_null hx)
  dpow_zero hx := Subtype.ext (hJ.dpow_zero hx)
  dpow_one hx := Subtype.ext (hJ.dpow_one hx)
  dpow_mem hn hx := hJ.dpow_mem hn hx
  dpow_add {n} x y hx hy := by
    apply Subtype.ext
    change hJ.dpow n ((x : B) + y) = (hJ.hull T).subtype _
    rw [map_sum]
    exact hJ.dpow_add hx hy
  dpow_mul hx := Subtype.ext (hJ.dpow_mul hx)
  mul_dpow hx := Subtype.ext (hJ.mul_dpow hx)
  dpow_comp hn hx := Subtype.ext (hJ.dpow_comp hn hx)

/-- The inclusion preserves the constructed divided-power operations. -/
theorem hullDividedPowers_coe (n : ℕ) (x : hJ.hull T) :
    ((hJ.hullDividedPowers T).dpow n x : B) = hJ.dpow n x := rfl

/-- Factorial denominators have their actual algebraic meaning in the hull. -/
theorem hull_factorial_mul_dpow (n : ℕ) {x : hJ.hull T}
    (hx : x ∈ hJ.hullIdeal T) :
    (n.factorial : hJ.hull T) * (hJ.hullDividedPowers T).dpow n x = x ^ n :=
  (hJ.hullDividedPowers T).factorial_mul_dpow_eq_pow hx

/-- An ambient map preserving the base and divided powers preserves the hull. -/
theorem map_mem_hull (f : B →+* B) (hT : T ≤ T.comap f)
    (hf : ∀ (n : ℕ) (x : B), x ∈ J → f (hJ.dpow n x) = hJ.dpow n (f x)) :
    hJ.hull T ≤ (hJ.hull T).comap f := by
  apply hJ.hull_le T
  · intro x hx
    exact hJ.le_hull T (hT hx)
  · intro n x hx hxJ
    change f (hJ.dpow n x) ∈ hJ.hull T
    rw [hf n x hxJ]
    exact hJ.dpow_mem_hull T n hx

end DividedPowers
