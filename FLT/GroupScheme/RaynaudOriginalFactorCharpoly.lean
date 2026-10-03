/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudOriginalOneWeight
public import FLT.GroupScheme.RaynaudOriginalTwoWeight
public import FLT.Deformations.RepresentationTheory.ScalarActionCharpoly

/-!
# Characteristic polynomials of original simple inertia factors

Combine constructed scalar characters and binary weights with the original
prime-field operator. No scalar model or factorization is an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ThreeAdicPlan
open NumberField IsLocalRing RaynaudParameters

variable {K : Type} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime]
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ωv" => AlgebraicClosure Kv
local notation "I" => localInertiaGroup v
local notation "Rsh" => unramifiedUnion (Ω := Ωv) (p : O)
local notation "Lsh" => FractionRing Rsh
local notation "Av" => IntegralClosure O Ωv

/-- Retain the canonical fraction-ring base algebra in the completion-field tower. -/
local instance factorCharpolyBaseAlgebra : Algebra O Lsh := inferInstance
variable [Algebra (v.adicCompletion K) (FractionRing (unramifiedUnion
    (Ω := AlgebraicClosure (v.adicCompletion K)) (p : v.adicCompletionIntegers K)))]
  [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K)
    (FractionRing (unramifiedUnion (Ω := AlgebraicClosure (v.adicCompletion K))
      (p : v.adicCompletionIntegers K)))]
  [HenselianLocalRing (v.adicCompletionIntegers K)]
  [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  (X : FF (v.adicCompletionIntegers K) (v.adicCompletion K))
  {U W : Type} [AddCommGroup U] [AddCommGroup W]
  [DistribMulAction (localInertiaGroup v) U] [DistribMulAction (localInertiaGroup v) W]
  [Module (ZMod p) W] [Module.Finite (ZMod p) W]
  (ρ : Representation (ZMod p) (localInertiaGroup v) W) [ρ.IsIrreducible]
  [TopologicalSpace (Module.End (ZMod p) W)ˣ] [DiscreteTopology (Module.End (ZMod p) W)ˣ]


/-- The original closure residue field retains the original residue characteristic. -/
local instance factorResidueCharP : CharP (ResidueField Av) p :=
  charP_of_injective_algebraMap
    (algebraMap (ResidueField O) (ResidueField Av)).injective p

set_option maxHeartbeats 1200000 in
-- The factor's derived scalar field is nested under the original tower instances.
/-- The original one-dimensional factor has the derived binary-weight charpoly. -/
theorem original_one_factor_charpoly (hp : Irreducible (p : O))
    (hρ : Continuous ρ.toHomUnits) (hact : ∀ σ w, ρ σ w = σ • w)
    (i : U →+[I] X.Points) (q : U →+[I] W)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hdimW : Module.finrank (ZMod p) W = 1)
    (e : Lsh →ₐ[Kv] Ωv) (he : ∀ a : Rsh, e (algebraMap Rsh Lsh a) = (a : Ωv))
    {α : Ωv} (hn : 0 < p - 1) (hp0 : (p : Kv) ≠ 0)
    (hα : α ^ (p - 1) = algebraMap Kv Ωv (p : Kv)) :
    ∃ d : ℕ, d ≤ 1 ∧ ∀ σ : I,
      (ρ σ).charpoly.map (ZMod.castHom (dvd_refl p) (ResidueField Av)) =
        Polynomial.X - Polynomial.C
          ((LocalRoot.character v hn hp0 hα σ : ResidueField Av) ^ d) := by
  obtain ⟨F, hF, hfin, hchar, hmod, χ, ε, d, hdim, hd, hχ, hw⟩ :=
    exists_original_one_weight v p X ρ hp hρ hact i q hi hq hdimW e he hn hp0 hα
  refine ⟨d, hd, fun σ ↦ ?_⟩
  have hs : ∀ w, ρ σ w = (χ σ : F) • w := fun w ↦ (hact σ w).trans (hχ σ w)
  have h := (ρ σ).charpoly_rank_one_scalar hdim (χ σ : F) hs ε hdimW
  have hc : ε.comp (ZMod.castHom (dvd_refl p) F) =
      ZMod.castHom (dvd_refl p) (ResidueField Av) := Subsingleton.elim _ _
  rwa [hc, hw σ] at h


set_option maxHeartbeats 1200000 in
-- The factor's derived scalar field is nested under the original tower instances.
/-- The original two-dimensional factor has the derived binary-weight charpoly. -/
theorem original_two_factor_charpoly (hp : Irreducible (p : O))
    (hρ : Continuous ρ.toHomUnits) (hact : ∀ σ w, ρ σ w = σ • w)
    (i : U →+[I] X.Points) (q : U →+[I] W)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hdimW : Module.finrank (ZMod p) W = 2)
    (e : Lsh →ₐ[Kv] Ωv) (he : ∀ a : Rsh, e (algebraMap Rsh Lsh a) = (a : Ωv))
    {α : Ωv} (hn : 0 < p * p - 1) (hp0 : (p : Kv) ≠ 0)
    (hα : α ^ (p * p - 1) = algebraMap Kv Ωv (p : Kv)) :
    ∃ a b : ℕ, a ≤ 1 ∧ b ≤ 1 ∧ ∀ σ : I,
      (ρ σ).charpoly.map (ZMod.castHom (dvd_refl p) (ResidueField Av)) =
        (Polynomial.X - Polynomial.C
          ((LocalRoot.character v hn hp0 hα σ : ResidueField Av) ^ (p * a + b))) *
        (Polynomial.X - Polynomial.C
          (((LocalRoot.character v hn hp0 hα σ : ResidueField Av) ^ (p * a + b)) ^ p)) := by
  obtain ⟨F, hF, hfin, hchar, hmod, χ, ε, a, b, hdim, ha, hb, hχ, hw⟩ :=
    exists_original_two_weight v p X ρ hp hρ hact i q hi hq hdimW e he hn hp0 hα
  refine ⟨a, b, ha, hb, fun σ ↦ ?_⟩
  have hs : ∀ w, ρ σ w = (χ σ : F) • w := fun w ↦ (hact σ w).trans (hχ σ w)
  have h := (ρ σ).charpoly_rank_two_scalar_factors hdim (χ σ : F) hs ε hdimW
  have hc : ε.comp (ZMod.castHom (dvd_refl p) F) =
      ZMod.castHom (dvd_refl p) (ResidueField Av) := Subsingleton.elim _ _
  rwa [hc, hw σ] at h

end ThreeAdicPlan
