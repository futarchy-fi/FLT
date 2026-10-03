/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudScalarCoordinateRatio
public import FLT.GroupScheme.RaynaudTowerAction
public import FLT.GroupScheme.RaynaudTowerResidue

/-!
# Identifying scalar values with original inertia ratios

For an actual scalar point action, reduction of its coordinate ratio is the
scalar's image under the compatible residue embedding. The root-character
formula can then be applied without identifying unrelated residue fields.
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
  [Field F] [Fintype F] [DecidableEq F]
  (X : FF R L) [Module F X.Points]
  (lift : F → ModelHom X X) (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdim : Module.finrank F X.Points = 1)
  (hlift : ∀ a x, genericHom (lift a) x = a • x)
  (ε : F →+* ResidueField R)
  (e : L →ₐ[v.adicCompletion K] AlgebraicClosure (v.adicCompletion K))

/-- A scalar point action identifies the original integral ratio in the correct residue field. -/
theorem FF.scalar_eq_original_ratio (x : X.Points) (hx : x ≠ 0)
    (σ : localInertiaGroup v) (hσ : ∀ a, σ.1 (e a) = e a) (u : Fˣ)
    (hu : towerAutomorphism e σ.1 hσ • x = (u : F) • x)
    (r : Av)
    (hr : r.val = σ.1 (towerClosureEquiv e
        (X.fundamentalValue lift h1 hmul p hdim hlift ε 0 x)) /
      towerClosureEquiv e (X.fundamentalValue lift h1 hmul p hdim hlift ε 0 x)) :
    towerResidueMap v e (ε u) = residue Av r := by
  have h := congrArg (towerClosureEquiv e)
    (X.fundamentalValue_ratio lift h1 hmul p hdim hlift ε 0 u x hx
      (towerAutomorphism e σ.1 hσ) hu)
  simp only [map_div₀, towerAutomorphism_apply, pow_zero, pow_one,
    IsScalarTower.algebraMap_apply R L (AlgebraicClosure L),
    towerClosureEquiv_algebraMap] at h
  have heq : r = towerIntegralMap v e (fundamentalCharacter p ε u : R) := by
    apply Subtype.ext
    exact hr.trans h
  rw [heq, ← towerResidueMap_residue, fundamentalCharacter_residue]

end ThreeAdicPlan
