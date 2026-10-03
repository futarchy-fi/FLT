/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudOriginalHigherWeight
public import FLT.GroupScheme.RaynaudPrescribedFraction
public import FLT.AbsoluteGaloisGroup.RationalPrimeUniformizer
public import FLT.AbsoluteGaloisGroup.FundamentalCyclotomic
public import FLT.AbsoluteGaloisGroup.InertiaDescentHenselian

/-!
# Original rational higher-factor weights

Construct the explicit tower algebra and embedding from the rational completion
and apply the arbitrary-dimensional original-factor weights. No tower is an input.
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
local notation "I" => localInertiaGroup v
local notation "Av" => IntegralClosure O Ωv
attribute [local instance] LocalRoot.rationalResidue_charP


variable (X : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ))
  {U W : Type} [AddCommGroup U] [AddCommGroup W]
  [DistribMulAction (localInertiaGroup (LocalCyclotomic.rationalPlace p)) U]
  [DistribMulAction (localInertiaGroup (LocalCyclotomic.rationalPlace p)) W]
  [Module (ZMod p) W]
  (ρ : Representation (ZMod p) (localInertiaGroup (LocalCyclotomic.rationalPlace p)) W)
  [ρ.IsIrreducible]
  [TopologicalSpace (Module.End (ZMod p) W)ˣ] [DiscreteTopology (Module.End (ZMod p) W)ˣ]

set_option maxHeartbeats 1600000 in
-- Construct the dependent fraction tower for the original arbitrary-dimensional factor.
/-- Original simple factors have higher binary weights over the rational completion. -/
theorem rational_original_higher_weight
    (hρ : Continuous ρ.toHomUnits) (hact : ∀ σ w, ρ σ w = σ • w)
    (i : U →+[I] X.Points) (q : U →+[I] W)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (r : ℕ+) (hdimW : Module.finrank (ZMod p) W = (r : ℕ))
    {α : Ωv} (hn : 0 < p ^ (r : ℕ) - 1) (hp0 : (p : Kv) ≠ 0)
    (hα : α ^ (p ^ (r : ℕ) - 1) = algebraMap Kv Ωv (p : Kv)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F p) (_ : Module F W)
      (χ : I →* Fˣ) (ε : F →+* ResidueField Av) (d : Fin r → ℕ),
      Module.finrank F W = 1 ∧ (∀ i, d i ≤ 1) ∧
      (∀ (σ : I) (w : W), σ • w = (χ σ : F) • w) ∧
      ∀ σ : I, ε (χ σ) = (LocalRoot.character v hn hp0 hα σ : ResidueField Av) ^
        (∑ i ∈ Finset.range (r : ℕ),
          d ⟨i % r, Nat.mod_lt _ r.pos⟩ * p ^ ((r : ℕ) - 1 - i)) := by
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
  exact exists_original_higher_weight v p X ρ (LocalCyclotomic.rationalPrime_irreducible p)
    hρ hact i q hi hq r hdimW e he hn hp0 hα

end ThreeAdicPlan
