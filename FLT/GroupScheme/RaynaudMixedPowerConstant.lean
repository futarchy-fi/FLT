/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudMixedCharacterAverage
public import FLT.GroupScheme.RaynaudPowerCharacterDifference
public import FLT.GroupScheme.RaynaudCharacterFactorial

/-!
# Mixed power constants as binomial products

Applying weighted differences in reverse list order removes the listed
weights successively. The resulting coefficient is an explicit natural
number, with no finite-flat model in its definition.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.CharacterAverage

variable {R F : Type*} [CommRing R] [Field F] [Fintype Fˣ]
  [Invertible (Fintype.card Fˣ : R)]

/-- Concatenating character lists composes their difference operators. -/
theorem mixed_append (cs ds : List (Fˣ →* Rˣ)) (f : F → R) :
    mixed (cs ++ ds) f = mixed cs (mixed ds f) := by
  induction cs with
  | nil => rfl
  | cons χ cs ih => simp only [List.cons_append, mixed_cons, ih]

/-- Mixed differences commute with multiplication by a scalar. -/
theorem mixed_smul (cs : List (Fˣ →* Rˣ)) (r : R) (f : F → R) :
    mixed cs (r • f) = r • mixed cs f := by
  induction cs with
  | nil => rfl
  | cons χ cs ih => rw [mixed_cons, ih, map_smul, ← mixed_cons]

/-- The binomial product for removing a list of weights with remainder n. -/
def weightCoefficient : List ℕ → ℕ → ℕ
  | [], _ => 1
  | k :: ks, n => (k + ks.sum + n).choose k * weightCoefficient ks n

variable [IsDomain R] (e : F →+* R)

/-- Mixed power-character differences remove precisely their total weight. -/
theorem mixed_power_monomial (ks : List ℕ) (n : ℕ)
    (hpos : ∀ k ∈ ks, 0 < k) (hq : ks.sum + n ≤ Fintype.card Fˣ) :
    mixed (ks.reverse.map (fun k ↦ embeddingCharacter e ^ k))
      (fun a ↦ e a ^ (ks.sum + n)) =
      (weightCoefficient ks n : R) • (fun a ↦ e a ^ n) := by
  induction ks with
  | nil => simp [mixed, weightCoefficient]
  | cons k ks ih =>
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      mixed_append, mixed_cons]
    have hm : k + ks.sum + n = k + (ks.sum + n) := Nat.add_assoc _ _ _
    simp only [List.sum_cons] at hq ⊢
    rw [hm, show mixed [] (fun a ↦ e a ^ (k + (ks.sum + n))) =
      (fun a ↦ e a ^ (k + (ks.sum + n))) from rfl,
      step_power_monomial e k (ks.sum + n) (hpos k (by simp)) (by omega), mixed_smul,
      ih (fun j hj ↦ hpos j (by simp [hj])) (by omega)]
    simp only [weightCoefficient, Nat.cast_mul, smul_smul, hm]

/-- A positive total weight gives the explicit mixed universal constant. -/
theorem mixed_power_constant (ks : List ℕ) (hpos : ∀ k ∈ ks, 0 < k)
    (hne : ks.sum ≠ 0) (hq : ks.sum ≤ Fintype.card Fˣ) :
    mixedConstant (ks.reverse.map (fun k ↦ embeddingCharacter e ^ k))
      (embeddingCharacter e ^ ks.sum) = (weightCoefficient ks 0 : R) := by
  unfold mixedConstant
  rw [show value (embeddingCharacter e ^ ks.sum) = (fun a ↦ e a ^ ks.sum) from
    funext (value_pow_embedding (embeddingCharacter e) e (fun _ ↦ rfl) _ hne)]
  have h := congrFun (mixed_power_monomial e ks 0 hpos (by simpa using hq)) 0
  simpa using h

end ThreeAdicPlan.CharacterAverage
