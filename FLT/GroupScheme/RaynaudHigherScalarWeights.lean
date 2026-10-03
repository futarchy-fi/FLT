/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudScalarCharacterBridge
public import FLT.GroupScheme.RaynaudHigherPointCharacter

/-!
# Higher-cycle scalar weights in the original residue field

Identify the transported point ratio with the actual scalar action, retaining
the common digits constructed from the original integral coefficients.
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
/-- Actual higher-cycle scalar actions have common original-inertia binary weights. -/
theorem FF.higher_cycle_scalar_weight
    (r : ℕ+) (hr : Fintype.card F = p ^ (r : ℕ)) (hp : Irreducible (p : R))
    (x : X.Points) (hx : x ≠ 0)
    {α : Ωv} (hn : 0 < p ^ (r : ℕ) - 1) (hp0 : (p : Kv) ≠ 0)
    (hα : α ^ (p ^ (r : ℕ) - 1) = algebraMap Kv Ωv (p : Kv)) :
    ∃ d : Fin r → ℕ, (∀ i, d i ≤ 1) ∧
      ∀ (σ : localInertiaGroup v) (hσ : ∀ z, σ.1 (e z) = e z) (u : Fˣ),
        towerAutomorphism e σ.1 hσ • x = (u : F) • x →
        towerResidueMap v e (ε u) =
          (LocalRoot.character v hn hp0 hα σ : ResidueField Av) ^
            (∑ i ∈ Finset.range (r : ℕ),
              d ⟨i % r, Nat.mod_lt _ r.pos⟩ * p ^ ((r : ℕ) - 1 - i)) := by
  obtain ⟨d, hd, hratio⟩ := X.fundamentalValue_cycle_original_character
    v lift h0 h1 hmul hadd p hdim hlift ε e r hr hp hn hp0 hα
  refine ⟨d, hd, fun σ hσ u hu ↦ ?_⟩
  obtain ⟨z, hzval, hzres⟩ := hratio x hx σ
  exact (X.scalar_eq_original_ratio v lift h1 hmul p hdim hlift ε e
    x hx σ hσ u hu z hzval).trans hzres

end ThreeAdicPlan
