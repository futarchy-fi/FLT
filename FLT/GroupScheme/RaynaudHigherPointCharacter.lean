/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudHigherBinaryPower
public import FLT.GroupScheme.RaynaudTowerRootCharacter

/-!
# Original inertia characters of arbitrary Raynaud cycles

The actual coefficient digits are chosen before the point and inertia element.
Transport the higher-cycle root equation through the prescribed closure map.
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
/-- Actual higher-cycle coordinates have common binary weights on original inertia. -/
theorem FF.fundamentalValue_cycle_original_character
    (r : ℕ+) (hr : Fintype.card F = p ^ (r : ℕ)) (hp : Irreducible (p : R))
    {α : Ωv} (hn : 0 < p ^ (r : ℕ) - 1) (hp0 : (p : Kv) ≠ 0)
    (hα : α ^ (p ^ (r : ℕ) - 1) = algebraMap Kv Ωv (p : Kv)) :
    ∃ d : Fin r → ℕ, (∀ i, d i ≤ 1) ∧
      ∀ (x : X.Points), x ≠ 0 → ∀ σ : localInertiaGroup v, ∃ z : Av,
        z.val = σ.1 (towerClosureEquiv e
            (X.fundamentalValue lift h1 hmul p hdim hlift ε 0 x)) /
          towerClosureEquiv e (X.fundamentalValue lift h1 hmul p hdim hlift ε 0 x) ∧
        residue Av z = (LocalRoot.character v hn hp0 hα σ : ResidueField Av) ^
          (∑ i ∈ Finset.range (r : ℕ),
            d ⟨i % r, Nat.mod_lt _ r.pos⟩ * p ^ ((r : ℕ) - 1 - i)) := by
  obtain ⟨d, u, hd, _, hu⟩ := X.fundamentalValue_cycle_binary
    lift h0 h1 hmul hadd p hdim hlift ε r hr hp
  exact ⟨d, hd, fun x hx σ ↦ exists_tower_coordinate_ratio v e
    (tower_coefficient_integral v e) hp0 hn hα _ (hu x hx) σ⟩

end ThreeAdicPlan
