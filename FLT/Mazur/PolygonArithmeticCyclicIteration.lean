/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCyclicCancellation

/-!
# Finite cyclic induction from the measured full edge errors

Each successor measures the actual preceding complete errors and constructs
its full node factors. The proof components are produced recursively from the
seed and the proved step; no all-layer correction witness is an input.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticCyclic
open PolygonArithmeticStages
variable {R : Type*} [CommRing R] {π : R} {ι : Type*}
  (σ : Equiv.Perm ι) (S : State R π ι) (hS : S.Compatible) (ha : S.Annihilated)
  (r₀ : ℕ) (hr₀ : S.Normalized r₀)

/-- Construct the finite states and prove their invariants together by natural recursion. -/
def State.iterateAux : (k : ℕ) →
    {U : State R π ι // U.Compatible ∧ U.Annihilated ∧ U.Normalized (r₀ + k)}
  | 0 => ⟨S, hS, ha, hr₀⟩
  | k + 1 =>
    let prev := State.iterateAux k
    let q := prev.val.nextIntegralField prev.property.1 (r₀ + k) prev.property.2.2
    ⟨prev.val.step σ q (r₀ + k),
      prev.val.step_compatible σ q (r₀ + k) prev.property.1,
      prev.val.step_annihilated σ q (r₀ + k) prev.property.2.1,
      prev.val.next_normalized σ prev.property.1 (r₀ + k) prev.property.2.2
        prev.property.2.1⟩

/-- Seal the finite construction so consumers do not expand all earlier corrections. -/
irreducible_def State.iterate (k : ℕ) : State R π ι :=
  (S.iterateAux σ hS ha r₀ hr₀ k).val

local notation "I" => S.iterate σ hS ha r₀ hr₀

/-- Every constructed finite state retains its exact coefficient quotients. -/
theorem State.iterate_compatible (k : ℕ) : (I k).Compatible := by
  rw [State.iterate_def]
  exact (S.iterateAux σ hS ha r₀ hr₀ k).property.1

/-- Every accumulated scalar drift retains the original annihilators. -/
theorem State.iterate_annihilated (k : ℕ) : (I k).Annihilated := by
  rw [State.iterate_def]
  exact (S.iterateAux σ hS ha r₀ hr₀ k).property.2.1

/-- All actual complete cyclic edges are normalized at every attained arithmetic layer. -/
theorem State.iterate_normalized (k : ℕ) : (I k).Normalized (r₀ + k) := by
  rw [State.iterate_def]
  exact (S.iterateAux σ hS ha r₀ hr₀ k).property.2.2

/-- The finite correction normalizes every earlier layer as well as its attained layer. -/
theorem State.iterate_normalized_le (k m : ℕ) (hm : m ≤ r₀ + k) :
    (I k).Normalized m :=
  (I k).normalized_restriction (S.iterate_compatible σ hS ha r₀ hr₀ k) hm
    (S.iterate_normalized σ hS ha r₀ hr₀ k)

/-- Zero further corrections recover the given concrete seed. -/
theorem State.iterate_zero : I 0 = S := by
  rw [State.iterate_def]
  rfl

/-- The fields for each successor are selected from the actual preceding finite state. -/
irreducible_def State.iterateField (k : ℕ) : ι → R[T;T⁻¹] :=
  let prev := S.iterateAux σ hS ha r₀ hr₀ k
  prev.val.nextIntegralField prev.property.1 (r₀ + k) prev.property.2.2

/-- Each successor applies the full simultaneous step on its actual preceding smoothings. -/
theorem State.iterate_succ (k : ℕ) :
    I (k + 1) = (I k).step σ (S.iterateField σ hS ha r₀ hr₀ k) (r₀ + k) := by
  simp only [State.iterateField_def, State.iterate_def, State.iterateAux]

end FLT.Mazur.PolygonArithmeticCyclic
