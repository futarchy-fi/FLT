/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudRankTwoCharpoly
public import FLT.GroupScheme.RaynaudPrescribedFraction
public import FLT.AbsoluteGaloisGroup.RationalPrimeUniformizer
public import FLT.AbsoluteGaloisGroup.FundamentalCyclotomic
public import FLT.AbsoluteGaloisGroup.InertiaDescentHenselian

/-!
# Original rational rank-two characteristic polynomials

Construct the explicit tower algebra and embedding from the rational completion
and apply the derived original-factor dichotomy. No tower is an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ThreeAdicPlan
open NumberField IsLocalRing RaynaudParameters

variable (p : ℕ) [Fact p.Prime]
local notation "v" => LocalCyclotomic.rationalPlace p
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "O" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "Ωv" => AlgebraicClosure Kv
local notation "k" => ResidueField (IntegralClosure O Ωv)
attribute [local instance] LocalRoot.rationalResidue_charP

set_option maxHeartbeats 1600000 in
-- Instantiate the dependent explicit fraction-field tower once for both cases.
/-- The original rational flat model yields binary factors without a supplied tower. -/
theorem rational_rank_two_charpoly (X : FF O Kv) [Module (ZMod p) X.Points]
    (ρ : Representation (ZMod p) (localInertiaGroup v) X.Points)
    (hρ : ρ.IsDiscreteContinuous) (hact : ∀ σ w, ρ σ w = σ • w)
    (hdim : Module.finrank (ZMod p) X.Points = 2)
    {α β : Ωv} (hn : 0 < p - 1) (hn2 : 0 < p * p - 1) (hp0 : (p : Kv) ≠ 0)
    (hα : α ^ (p - 1) = algebraMap Kv Ωv (p : Kv))
    (hβ : β ^ (p * p - 1) = algebraMap Kv Ωv (p : Kv)) :
    (∃ a b : ℕ, a ≤ 1 ∧ b ≤ 1 ∧ ∀ σ : localInertiaGroup v,
      (ρ σ).charpoly.map (ZMod.castHom (dvd_refl p) k) =
        (Polynomial.X - Polynomial.C ((LocalRoot.character v hn hp0 hα σ : k) ^ a)) *
        (Polynomial.X - Polynomial.C ((LocalRoot.character v hn hp0 hα σ : k) ^ b))) ∨
    (∃ a b : ℕ, a ≤ 1 ∧ b ≤ 1 ∧ ∀ σ : localInertiaGroup v,
      (ρ σ).charpoly.map (ZMod.castHom (dvd_refl p) k) =
        (Polynomial.X - Polynomial.C
          ((LocalRoot.character v hn2 hp0 hβ σ : k) ^ (p * a + b))) *
        (Polynomial.X - Polynomial.C
          (((LocalRoot.character v hn2 hp0 hβ σ : k) ^ (p * a + b)) ^ p))) := by
  let : CharP (ResidueField O) p := (LocalCyclotomic.residueEquiv p).toRingHom.charP
    (LocalCyclotomic.residueEquiv p).injective p
  let : IsAdicComplete (maximalIdeal O) O := rationalCompletionIntegers_adicComplete p
  let : HenselianLocalRing O := by
    constructor
    intro f hf x hx hd
    exact HenselianRing.is_henselian f hf x hx (hd.map (Ideal.Quotient.mk (maximalIdeal O)))
  obtain ⟨hKL, hT, e, he⟩ := exists_subalgebra_fraction_embedding
    (K := Kv) (unramifiedUnion (Ω := Ωv) (p : O))
  let := hKL
  let := hT
  exact original_rank_two_charpoly v p X ρ (LocalCyclotomic.rationalPrime_irreducible p)
    hρ hact hdim e he hn hn2 hp0 hα hβ

end ThreeAdicPlan
