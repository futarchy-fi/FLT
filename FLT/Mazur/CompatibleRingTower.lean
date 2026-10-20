/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Rings and homogeneous ideals of compatible full section towers

Compatibility is imposed at every comparable pair of orders. The ideal
retains the entire prescribed ideal at each order. Mapping a tower uses
actual commuting restriction squares, not independent choices of lifts.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.CompatibleRingTower
variable {R S : ℕ → Type*} [∀ k, CommRing (R k)] [∀ k, CommRing (S k)]
  (ρ : ∀ k l, k ≤ l → R l →+* R k)

/-- Full section families satisfying every order transition. -/
def ring : Subring (∀ k, R k) where
  carrier := {v | ∀ k l (h : k ≤ l), ρ k l h (v l) = v k}
  zero_mem' := fun _ _ _ ↦ map_zero _
  one_mem' := fun _ _ _ ↦ map_one _
  add_mem' := by
    intro v w hv hw k l h
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) (hv k l h) (hw k l h))
  mul_mem' := by
    intro v w hv hw k l h
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (hv k l h) (hw k l h))
  neg_mem' := by
    intro v hv k l h
    exact (map_neg _ _).trans (congrArg Neg.neg (hv k l h))

/-- Evaluation at a fixed original order. -/
def eval (k : ℕ) : ring ρ →+* R k :=
  (Pi.evalRingHom R k).comp (ring ρ).subtype

/-- The full homogeneous ideal, with no radical or reduction of any stage. -/
def ideal (I : ∀ k, Ideal (R k)) : Ideal (ring ρ) where
  carrier := {v | ∀ k, v.val k ∈ I k}
  zero_mem' := fun k ↦ (I k).zero_mem
  add_mem' hv hw := fun k ↦ (I k).add_mem (hv k) (hw k)
  smul_mem' a _ hv := fun k ↦ (I k).mul_mem_left (a.val k) (hv k)

/-- Membership keeps the specified full ideal at every order. -/
theorem mem_ideal (I : ∀ k, Ideal (R k)) (v : ring ρ) :
    v ∈ ideal ρ I ↔ ∀ k, v.val k ∈ I k := Iff.rfl

variable (σ : ∀ k l, k ≤ l → S l →+* S k) (f : ∀ k, R k →+* S k)
  (hsq : ∀ k l (h : k ≤ l) z, f k (ρ k l h z) = σ k l h (f l z))

/-- Commuting full restriction maps assemble to a map of compatible rings. -/
def map : ring ρ →+* ring σ where
  toFun v := ⟨fun k ↦ f k (v.val k), fun k l h ↦ by
    rw [← hsq, v.property k l h]⟩
  map_zero' := Subtype.ext (funext fun k ↦ map_zero (f k))
  map_one' := Subtype.ext (funext fun k ↦ map_one (f k))
  map_add' v w := Subtype.ext (funext fun k ↦ map_add (f k) _ _)
  map_mul' v w := Subtype.ext (funext fun k ↦ map_mul (f k) _ _)

/-- Assembly preserves every literal coefficient value. -/
theorem map_apply (v : ring ρ) (k : ℕ) :
    (map ρ σ f hsq v).val k = f k (v.val k) := rfl

/-- Stagewise ideal preservation gives ideal preservation for the whole tower. -/
theorem map_mem_ideal (I : ∀ k, Ideal (R k)) (J : ∀ k, Ideal (S k))
    (hIJ : ∀ k z, z ∈ I k → f k z ∈ J k) (v : ring ρ) (hv : v ∈ ideal ρ I) :
    map ρ σ f hsq v ∈ ideal σ J := fun k ↦ hIJ k (v.val k) (hv k)

end FLT.Mazur.CompatibleRingTower
