/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudScalarCharacterBridge
public import FLT.GroupScheme.RaynaudTowerPointCharacter

/-!
# Binary weights for actual scalar actions in the original residue field

Combine point equations and scalar-coordinate evaluation. Digits are derived
once and work for every original inertia element fixing the tower.
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

include h0 h1 hmul hadd hdim hlift in
/-- Actual scalar actions on a one-cycle model have a common binary original-root weight. -/
theorem FF.one_cycle_scalar_weight (hp : Irreducible (p : R))
    (hr : Fintype.card F = p ^ (1 : ℕ)) (x : X.Points) (hx : x ≠ 0)
    {α : Ωv} (hn : 0 < p - 1) (hp0 : (p : Kv) ≠ 0)
    (hα : α ^ (p - 1) = algebraMap Kv Ωv (p : Kv)) :
    ∃ d : ℕ, d ≤ 1 ∧ ∀ (σ : localInertiaGroup v) (hσ : ∀ a, σ.1 (e a) = e a)
      (u : Fˣ), towerAutomorphism e σ.1 hσ • x = (u : F) • x →
      towerResidueMap v e (ε u) =
        (LocalRoot.character v hn hp0 hα σ : ResidueField Av) ^ d := by
  obtain ⟨d, hd, hratio⟩ := X.fundamentalValue_one_original_character
    v lift h0 h1 hmul hadd p hdim hlift ε e hp hr x hx hn hp0 hα
  refine ⟨d, hd, fun σ hσ u hu ↦ ?_⟩
  obtain ⟨r, hrval, hrres⟩ := hratio σ
  exact (X.scalar_eq_original_ratio v lift h1 hmul p hdim hlift ε e
    x hx σ hσ u hu r hrval).trans hrres

include h0 h1 hmul hadd hdim hlift in
/-- Actual scalar actions on a two-cycle model have common Frobenius-weighted binary digits. -/
theorem FF.two_cycle_scalar_weight (hp : Irreducible (p : R))
    (hr : Fintype.card F = p ^ (2 : ℕ)) (x : X.Points) (hx : x ≠ 0)
    {α : Ωv} (hn : 0 < p * p - 1) (hp0 : (p : Kv) ≠ 0)
    (hα : α ^ (p * p - 1) = algebraMap Kv Ωv (p : Kv)) :
    ∃ a b : ℕ, a ≤ 1 ∧ b ≤ 1 ∧
      ∀ (σ : localInertiaGroup v) (hσ : ∀ z, σ.1 (e z) = e z) (u : Fˣ),
      towerAutomorphism e σ.1 hσ • x = (u : F) • x →
      towerResidueMap v e (ε u) =
        (LocalRoot.character v hn hp0 hα σ : ResidueField Av) ^ (p * a + b) := by
  obtain ⟨a, b, ha, hb, hratio⟩ := X.fundamentalValue_two_original_character
    v lift h0 h1 hmul hadd p hdim hlift ε e hp hr x hx hn hp0 hα
  refine ⟨a, b, ha, hb, fun σ hσ u hu ↦ ?_⟩
  obtain ⟨r, hrval, hrres⟩ := hratio σ
  exact (X.scalar_eq_original_ratio v lift h1 hmul p hdim hlift ε e
    x hx σ hσ u hu r hrval).trans hrres

end ThreeAdicPlan
