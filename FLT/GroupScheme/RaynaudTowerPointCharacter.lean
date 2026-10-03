/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudPointPower
public import FLT.GroupScheme.RaynaudTowerRootCharacter

/-!
# Original root characters of actual Raynaud point coordinates

Binary exponents come from the actual coordinate equations. Integral tower
coefficients and the prescribed closure embedding give ratios for every
original inertia element, with one common choice of digits.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open NumberField IsLocalRing RaynaudParameters

variable {K : Type} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ωv" => AlgebraicClosure Kv
local notation "Av" => IntegralClosure O Ωv

variable {R L F : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field L] [Algebra R L]
  [CharZero L] [IsFractionRing R L] [Algebra (v.adicCompletion K) L]
  [Algebra (v.adicCompletionIntegers K) R]
  [Algebra.IsIntegral (v.adicCompletionIntegers K) R]
  [Algebra (v.adicCompletionIntegers K) L]
  [IsScalarTower (v.adicCompletionIntegers K) R L]
  [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) L]
  [Field F] [Fintype F] [DecidableEq F] [Invertible (Fintype.card Fˣ : R)]
  (X : FF R L) [Module F X.Points]
  (lift : F → ModelHom X X) (h0 : lift 0 = ModelHom.zero X X)
  (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
  (hadd : ∀ a b, lift (a + b) = (lift a).add (lift b))
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdim : Module.finrank F X.Points = 1)
  (hlift : ∀ a x, genericHom (lift a) x = a • x)
  (ε : F →+* ResidueField R) (e : L →ₐ[(v.adicCompletion K)] AlgebraicClosure (v.adicCompletion K))

include h0 hadd in
/-- An actual one-cycle coordinate has a common binary original-inertia weight. -/
theorem FF.fundamentalValue_one_original_character (hp : Irreducible (p : R))
    (hr : Fintype.card F = p ^ (1 : ℕ)) (x : X.Points) (hx : x ≠ 0)
    {α : Ωv} (hn : 0 < p - 1) (hp0 : (p : Kv) ≠ 0)
    (hα : α ^ (p - 1) = algebraMap Kv Ωv (p : Kv)) :
    ∃ d : ℕ, d ≤ 1 ∧ ∀ σ : localInertiaGroup v, ∃ r : Av,
      r.val = σ.1 (towerClosureEquiv e (X.fundamentalValue lift h1 hmul p hdim hlift ε 0 x)) /
        towerClosureEquiv e (X.fundamentalValue lift h1 hmul p hdim hlift ε 0 x) ∧
      residue Av r = (LocalRoot.character v hn hp0 hα σ : ResidueField Av) ^ d := by
  obtain ⟨d, u, hd, hu⟩ := X.fundamentalValue_one_binary
    lift h0 h1 hmul hadd p hdim hlift ε hp hr x hx
  exact ⟨d, hd, fun σ ↦ exists_tower_coordinate_ratio v e
    (tower_coefficient_integral v e) hp0 hn hα u hu σ⟩

include h0 hadd in
/-- An actual two-cycle coordinate has common Frobenius-weighted binary inertia digits. -/
theorem FF.fundamentalValue_two_original_character (hp : Irreducible (p : R))
    (hr : Fintype.card F = p ^ (2 : ℕ)) (x : X.Points) (hx : x ≠ 0)
    {α : Ωv} (hn : 0 < p * p - 1) (hp0 : (p : Kv) ≠ 0)
    (hα : α ^ (p * p - 1) = algebraMap Kv Ωv (p : Kv)) :
    ∃ a b : ℕ, a ≤ 1 ∧ b ≤ 1 ∧ ∀ σ : localInertiaGroup v, ∃ r : Av,
      r.val = σ.1 (towerClosureEquiv e (X.fundamentalValue lift h1 hmul p hdim hlift ε 0 x)) /
        towerClosureEquiv e (X.fundamentalValue lift h1 hmul p hdim hlift ε 0 x) ∧
      residue Av r = (LocalRoot.character v hn hp0 hα σ : ResidueField Av) ^ (p * a + b) := by
  obtain ⟨a, b, u, ha, hb, hu⟩ := X.fundamentalValue_two_binary
    lift h0 h1 hmul hadd p hdim hlift ε hp hr x hx
  exact ⟨a, b, ha, hb, fun σ ↦ exists_tower_coordinate_ratio v e
    (tower_coefficient_integral v e) hp0 hn hα u hu σ⟩

end ThreeAdicPlan
