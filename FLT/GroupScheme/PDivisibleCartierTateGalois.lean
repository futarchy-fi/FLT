/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCartierTatePairing
public import FLT.GroupScheme.RaynaudCartierPairingGalois
public import FLT.GroupScheme.RaynaudCartierCharacters

/-! # Galois-equivariant Cartier evaluation into coherent p-power roots -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)

/-- The paired sequence belongs to the actual inverse limit of p-power roots of unity. -/
def cartierTateRoots (y : X.CartierTate) (x : X.tateSequences) :
    {z : ℕ → (AlgebraicClosure K)ˣ //
      (∀ n, z n ^ (p ^ n) = 1) ∧ ∀ {m n}, m ≤ n → z n ^ (p ^ (n - m)) = z m} :=
  ⟨X.cartierTatePairing y x, fun n ↦ X.cartierTateLevelPairing_pow n y (X.tateEval n x),
    fun h ↦ X.cartierTatePairing_transition h y x⟩

/-- The inverse-limit root value at each level is the original finite Cartier pairing. -/
@[simp] theorem cartierTateRoots_eval (y : X.CartierTate) (x : X.tateSequences) (n : ℕ) :
    (X.cartierTateRoots y x).val n =
      (X.level n).cartierPairing (X.cartierTateEval n y) (X.tateEval n x) := rfl

/-- The dual inverse-limit evaluation respects the actual local Galois action. -/
theorem cartierTateEval_smul (σ : Field.absoluteGaloisGroup K)
    (y : X.CartierTate) (n : ℕ) :
    X.cartierTateEval n (σ • y) = σ • X.cartierTateEval n y := rfl

/-- Simultaneous conjugation of the two Tate vectors conjugates each paired root. -/
theorem cartierTatePairing_smul (σ : Field.absoluteGaloisGroup K)
    (y : X.CartierTate) (x : X.tateSequences) (n : ℕ) :
    X.cartierTatePairing (σ • y) (σ • x) n = σ • X.cartierTatePairing y x n :=
  (X.level n).cartierPairing_smul σ (X.cartierTateEval n y) (X.tateEval n x)

/-- Addition of original Tate vectors multiplies their coherent root sequences. -/
theorem cartierTatePairing_add_right (y : X.CartierTate) (x z : X.tateSequences) (n : ℕ) :
    X.cartierTatePairing y (x + z) n =
      X.cartierTatePairing y x n * X.cartierTatePairing y z n :=
  (X.level n).cartierPairing_add_right (X.cartierTateEval n y) (X.tateEval n x) (X.tateEval n z)

/-- Addition of dual Tate vectors multiplies their coherent root sequences. -/
theorem cartierTatePairing_add_left (y z : X.CartierTate) (x : X.tateSequences) (n : ℕ) :
    X.cartierTatePairing (y + z) x n =
      X.cartierTatePairing y x n * X.cartierTatePairing z x n :=
  (X.level n).cartierPairing_add_left (X.cartierTateEval n y) (X.cartierTateEval n z)
    (X.tateEval n x)

/-- All original finite-level Cartier evaluations separate dual Tate vectors. -/
theorem cartierTateLevelPairing_separates {y z : X.CartierTate}
    (h : ∀ n (x : (X.level n).Points),
      X.cartierTateLevelPairing n y x = X.cartierTateLevelPairing n z x) : y = z := by
  apply X.cartierDual.tate_ext
  intro n
  exact (X.level n).cartierPairing_separates_dual (h n)

end ThreeAdicPlan.PDivisibleSystem
