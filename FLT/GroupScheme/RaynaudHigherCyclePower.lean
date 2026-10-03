/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudEvaluatedCycle
public import FLT.GroupScheme.CyclicPowerElimination

/-!
# Root equations for actual higher Raynaud cycles

Evaluate every actual cyclic relation and eliminate the entire cycle. The
coefficients are those constructed from the original scalar model.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R K F : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K] [Field F] [Fintype F] [DecidableEq F]
  (X : FF R K) [Module F X.Points]
  (lift : F → ModelHom X X) (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdim : Module.finrank F X.Points = 1)
  (hlift : ∀ a x, genericHom (lift a) x = a • x) (e : F →+* ResidueField R)

/-- An actual nonzero coordinate satisfies the full higher-niveau root equation. -/
theorem FF.fundamentalValue_cycle (r : ℕ+) (hr : Fintype.card F = p ^ (r : ℕ))
    (x : X.Points) (hx : x ≠ 0) :
    X.fundamentalValue lift h1 hmul p hdim hlift e 0 x ^ (p ^ (r : ℕ) - 1) =
      algebraMap R (AlgebraicClosure K)
        (∏ i ∈ Finset.range (r : ℕ),
          (X.fundamentalCoefficient lift h1 hmul p hdim hlift e r hr
            ⟨i % r, Nat.mod_lt _ r.pos⟩) ^ (p ^ ((r : ℕ) - 1 - i))) := by
  let y : ℕ → AlgebraicClosure K := fun i ↦
    X.fundamentalValue lift h1 hmul p hdim hlift e (i % r) x
  let a : ℕ → R := fun i ↦
    X.fundamentalCoefficient lift h1 hmul p hdim hlift e r hr
      ⟨i % r, Nat.mod_lt _ r.pos⟩
  have hy : y 0 ≠ 0 := by
    simpa only [y, Nat.zero_mod, FF.fundamentalValue] using
      X.fundamentalCoordinate_eval_ne_zero lift h1 hmul hlift p hdim e 0 x hx
  have heq (i : ℕ) (hi : i < r) :
      y i ^ p = algebraMap R (AlgebraicClosure K) (a i) * y (i + 1) := by
    simpa only [y, a, Nat.mod_eq_of_lt hi, cycleNext] using
      X.fundamentalValue_power lift h1 hmul p hdim hlift e r hr ⟨i, hi⟩ x
  have h := RaynaudParameters.coordinate_cycle_power p r
    (CharP.char_is_prime F p).one_lt.le y
    (fun i ↦ algebraMap R (AlgebraicClosure K) (a i)) hy
    (by simp only [y, Nat.mod_self, Nat.zero_mod]) heq
  simpa only [y, a, Nat.zero_mod, map_prod, map_pow] using h

end ThreeAdicPlan
