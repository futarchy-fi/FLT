/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSimultaneousCancellation

/-!
# Finite simultaneous induction with measured fields and changing smoothings

Each successor measures the actual preceding complete errors and constructs
its full node factors. The proof components are produced recursively from the
seed and the proved step; no all-layer correction witness is an input.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticSimultaneous
open PolygonArithmeticStages
variable {R : Type*} [CommRing R] {π : R}
  (B : (m : ℕ) → (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])
  (hB : CompatibleEquiv B) (hb : ReciprocalBase B)
  (S : State R π) (hS : S.Compatible) (ha : S.Annihilated)
  (r₀ : ℕ) (hr₀ : S.Normalized B r₀)

/-- Construct the finite states and prove their invariants together by natural recursion. -/
def State.iterateAux : (k : ℕ) →
    {U : State R π // U.Compatible ∧ U.Annihilated ∧ U.Normalized B (r₀ + k)}
  | 0 => ⟨S, hS, ha, hr₀⟩
  | k + 1 =>
    let prev := State.iterateAux k
    let q := prev.val.nextIntegralField B prev.property.1 hB (r₀ + k) prev.property.2.2
    ⟨prev.val.step (r₀ + k) q,
      prev.val.step_compatible (r₀ + k) q prev.property.1,
      prev.val.step_annihilated (r₀ + k) q prev.property.2.1,
      prev.val.next_normalized B prev.property.1 hB (r₀ + k) prev.property.2.2
        prev.property.2.1 hb⟩

/-- Seal the finite construction so consumers do not expand all earlier corrections. -/
irreducible_def State.iterate (k : ℕ) : State R π :=
  (S.iterateAux B hB hb hS ha r₀ hr₀ k).val

local notation "I" => S.iterate B hB hb hS ha r₀ hr₀

/-- Every constructed finite state retains its exact coefficient quotients. -/
theorem State.iterate_compatible (k : ℕ) : (I k).Compatible := by
  rw [State.iterate_def]
  exact (S.iterateAux B hB hb hS ha r₀ hr₀ k).property.1

/-- Every accumulated scalar drift retains the original annihilators. -/
theorem State.iterate_annihilated (k : ℕ) : (I k).Annihilated := by
  rw [State.iterate_def]
  exact (S.iterateAux B hB hb hS ha r₀ hr₀ k).property.2.1

/-- Both actual complete residuals are normalized at every attained arithmetic layer. -/
theorem State.iterate_normalized (k : ℕ) : (I k).Normalized B (r₀ + k) := by
  rw [State.iterate_def]
  exact (S.iterateAux B hB hb hS ha r₀ hr₀ k).property.2.2

/-- The finite correction normalizes every earlier layer as well as its attained layer. -/
theorem State.iterate_normalized_le (k m : ℕ) (hm : m ≤ r₀ + k) :
    (I k).Normalized B m :=
  (I k).normalized_restriction B (S.iterate_compatible B hB hb hS ha r₀ hr₀ k) hB hm
    (S.iterate_normalized B hB hb hS ha r₀ hr₀ k)

/-- Zero further corrections recover the given concrete seed. -/
theorem State.iterate_zero : I 0 = S := by
  rw [State.iterate_def]
  rfl

/-- The fields for each successor are selected from the actual preceding finite state. -/
irreducible_def State.iterateField (k : ℕ) : Bool → Bool → R[T;T⁻¹] :=
  let prev := S.iterateAux B hB hb hS ha r₀ hr₀ k
  prev.val.nextIntegralField B prev.property.1 hB (r₀ + k) prev.property.2.2

/-- Each successor applies the full simultaneous step on its actual preceding smoothings. -/
theorem State.iterate_succ (k : ℕ) :
    I (k + 1) = (I k).step (r₀ + k) (S.iterateField B hB hb hS ha r₀ hr₀ k) := by
  simp only [State.iterateField_def, State.iterate_def, State.iterateAux]

/-- Every finite last smoothing retains the complete next incoming linear drift. -/
theorem State.iterate_last_succ (k m : ℕ) (b : Bool) :
    (I (k + 1)).last m b =
      (1 - parameter R π m ^ (r₀ + k + 1) * algebraMap R (Quotient R π m)
        ((S.iterateField B hB hb hS ha r₀ hr₀ k false b).coeff 1)) * (I k).last m b := by
  rw [State.iterate_succ, State.step_last]

end FLT.Mazur.PolygonArithmeticSimultaneous
