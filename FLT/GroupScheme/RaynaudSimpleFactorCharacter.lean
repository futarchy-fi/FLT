/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudSimpleFactorTower
public import FLT.GroupScheme.RaynaudMaximalScalarModel
public import FLT.GroupScheme.RaynaudTowerScalarWeights
public import FLT.Deformations.RepresentationTheory.RankOneScalarCharacter

/-!
# Original simple-factor scalar characters and local models

Construct a scalar character and a maximal model from the original simple
factor. Every original inertia element acts through that same character.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ThreeAdicPlan
open NumberField IsLocalRing RaynaudParameters

variable {K : Type} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ωv" => AlgebraicClosure Kv
local notation "I" => localInertiaGroup v
variable {π : v.adicCompletionIntegers K} (hπ : Irreducible π)
local notation "Rsh" => unramifiedUnion (Ω := Ωv) π
local notation "Lsh" => FractionRing Rsh

/-- Retain the canonical fraction-ring base algebra in the completion-field tower. -/
local instance weightTowerBaseAlgebra : Algebra O Lsh := inferInstance
variable [Algebra (v.adicCompletion K) (FractionRing
    (unramifiedUnion (Ω := AlgebraicClosure (v.adicCompletion K)) π))]
  [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) (FractionRing
    (unramifiedUnion (Ω := AlgebraicClosure (v.adicCompletion K)) π))]
  [HenselianLocalRing (v.adicCompletionIntegers K)]
  (X : FF (v.adicCompletionIntegers K) (v.adicCompletion K))
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  {U W : Type} [AddCommGroup U] [AddCommGroup W]
  [DistribMulAction (localInertiaGroup v) U] [DistribMulAction (localInertiaGroup v) W]
  [Module (ZMod p) W]
  (ρ : Representation (ZMod p) (localInertiaGroup v) W) [ρ.IsIrreducible]
  [TopologicalSpace (Module.End (ZMod p) W)ˣ] [DiscreteTopology (Module.End (ZMod p) W)ˣ]

-- Elaborating the nested model witnesses and fraction-field instances needs this budget.
set_option maxHeartbeats 1200000 in
-- Nested model witnesses contain several dependent fraction-field algebra instances.
include hπ in
/-- Derive the original factor's scalar character and its actual integral scalar model. -/
theorem exists_simple_factor_character_model
    (hρ : Continuous ρ.toHomUnits) (hact : ∀ σ w, ρ σ w = σ • w)
    (i : U →+[I] X.Points) (q : U →+[I] W)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (e : Lsh →ₐ[Kv] Ωv) (he : ∀ a : Rsh, e (algebraMap Rsh Lsh a) = (a : Ωv)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F p) (_ : Module F W)
      (χ : I →* Fˣ) (M : FF Rsh Lsh) (_ : Module F M.Points)
      (_f : W ≃ₗ[F] M.Points) (lift : F → ModelHom M M),
      Module.finrank F W = 1 ∧ Module.finrank F M.Points = 1 ∧
      (∀ (σ : I) (w : W), σ • w = (χ σ : F) • w) ∧
      (∀ (σ : I) (x : M.Points), originalTowerInertia v π e he σ • x = (χ σ : F) • x) ∧
      (∀ a x, genericHom (lift a) x = a • x) ∧
      lift 0 = ModelHom.zero M M ∧ lift 1 = BialgHom.id Rsh M.CoordinateRing ∧
      (∀ a b, lift (a + b) = (lift a).add (lift b)) ∧
      (∀ a b, lift (a * b) = (lift b).comp (lift a)) := by
  let : IsDiscreteValuationRing Rsh := unramifiedUnion_dvr hπ
  let : CharZero Lsh := charZero_of_injective_algebraMap (algebraMap Kv Lsh).injective
  obtain ⟨F, hF, hfin, hp, hmod, d, hflat, hdim, hcomm, hmatch⟩ :=
    exists_simple_factor_tower v hπ X p ρ hρ hact i q hi hq e he
  let := d
  let := hcomm
  obtain ⟨χ, hχ⟩ := Representation.exists_rank_one_scalar_character (G :=
    AlgebraicClosure Lsh ≃ₐ[Lsh] AlgebraicClosure Lsh) hdim
  obtain ⟨M, hmodM, f, lift, hf, hdimM, hlift, h0, h1, hadd, hmul, _⟩ :=
    exists_maximal_scalar_model hflat hdim
  refine ⟨F, hF, hfin, hp, hmod, χ.comp (originalTowerInertia v π e he),
    M, hmodM, f, lift, hdim, hdimM, ?_, ?_, hlift, h0, h1, hadd, hmul⟩
  · intro σ w
    exact (hmatch σ w).symm.trans (hχ _ w)
  · intro σ x
    obtain ⟨w, rfl⟩ := f.surjective x
    exact (hf _ w).symm.trans ((congrArg f (hχ _ w)).trans (f.map_smul _ w))

end ThreeAdicPlan
