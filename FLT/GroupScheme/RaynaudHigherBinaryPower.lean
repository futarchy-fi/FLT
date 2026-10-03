/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudHigherCyclePower
public import FLT.GroupScheme.RaynaudValuationDigits

/-!
# Binary-weight equations for arbitrary Raynaud cycles

Choose digits and units from every actual coefficient. Their weighted product
gives the root equation with one common set of digits for every nonzero point.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R K F : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K] [Field F] [Fintype F] [DecidableEq F]
  [Invertible (Fintype.card Fˣ : R)] (X : FF R K) [Module F X.Points]
  (lift : F → ModelHom X X) (h0 : lift 0 = ModelHom.zero X X)
  (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
  (hadd : ∀ a b, lift (a + b) = (lift a).add (lift b))
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdim : Module.finrank F X.Points = 1)
  (hlift : ∀ a x, genericHom (lift a) x = a • x) (e : F →+* ResidueField R)

include h0 hadd in
/-- Every actual higher cycle has common binary digits and the corresponding unit product. -/
theorem FF.fundamentalValue_cycle_binary (r : ℕ+) (hr : Fintype.card F = p ^ (r : ℕ))
    (hp : Irreducible (p : R)) :
    ∃ (d : Fin r → ℕ) (u : Fin r → Rˣ), (∀ i, d i ≤ 1) ∧
      (∀ i, X.fundamentalCoefficient lift h1 hmul p hdim hlift e r hr i =
        (p : R) ^ d i * u i) ∧
      ∀ (x : X.Points), x ≠ 0 →
        X.fundamentalValue lift h1 hmul p hdim hlift e 0 x ^ (p ^ (r : ℕ) - 1) =
          algebraMap R (AlgebraicClosure K)
            ((p : R) ^ (∑ i ∈ Finset.range (r : ℕ),
              d ⟨i % r, Nat.mod_lt _ r.pos⟩ * p ^ ((r : ℕ) - 1 - i)) *
              ↑(∏ i ∈ Finset.range (r : ℕ),
                u ⟨i % r, Nat.mod_lt _ r.pos⟩ ^ (p ^ ((r : ℕ) - 1 - i)))) := by
  classical
  choose d u hd hu using X.fundamentalCoefficient_eq_prime_pow_mul_unit
    lift h0 h1 hmul hadd p hdim hlift e r hr hp
  refine ⟨d, u, hd, hu, fun x hx ↦ ?_⟩
  rw [X.fundamentalValue_cycle lift h1 hmul p hdim hlift e r hr x hx]
  congr 1
  simp only [hu, mul_pow, ← pow_mul, Finset.prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum,
    Units.coe_prod, Units.val_pow_eq_pow_val]

end ThreeAdicPlan
