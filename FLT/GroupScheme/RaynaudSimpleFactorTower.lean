/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudInertiaFactorDescent
public import FLT.GroupScheme.RaynaudOriginalFactorTransport

/-!
# Original simple inertia factors on the prescribed tower

Construct the finite scalar field and finite descent from the actual simple
subquotient, then transport its model while retaining every original inertia action.
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
local instance simpleTowerBaseAlgebra : Algebra O Lsh := inferInstance
variable [Algebra (v.adicCompletion K) (FractionRing
    (unramifiedUnion (Ω := AlgebraicClosure (v.adicCompletion K)) π))]
  [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) (FractionRing
    (unramifiedUnion (Ω := AlgebraicClosure (v.adicCompletion K)) π))]
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
/-- Original simple subquotients acquire rank-one scalar models on the actual tower. -/
theorem exists_simple_factor_tower
    (hρ : Continuous ρ.toHomUnits) (hact : ∀ σ w, ρ σ w = σ • w)
    (i : U →+[I] X.Points) (q : U →+[I] W)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (e : Lsh →ₐ[Kv] Ωv) (he : ∀ a : Rsh, e (algebraMap Rsh Lsh a) = (a : Ωv)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F p) (_ : Module F W)
      (d : DistribMulAction (AlgebraicClosure Lsh ≃ₐ[Lsh] AlgebraicClosure Lsh) W),
      letI := d
      GaloisModule.IsFiniteFlat Rsh Lsh (AlgebraicClosure Lsh) W ∧
      Module.finrank F W = 1 ∧
      SMulCommClass F (AlgebraicClosure Lsh ≃ₐ[Lsh] AlgebraicClosure Lsh) W ∧
      ∀ (σ : I) (w : W), originalTowerInertia v π e he σ • w = σ • w := by
  obtain ⟨F, hF, hfin, hp, hmod, dU, dW, hflat, hdim, hcomm, hmatch⟩ :=
    exists_simple_factor_scalar_descent v X p ρ hρ hact i q hi hq
  let := dU
  let := dW
  let := hcomm
  obtain ⟨d, hflat', hcomm', hmatch'⟩ :=
    exists_original_factor_tower_action (X := X.Points) (F := F) v hπ hflat hmatch e he
  exact ⟨F, hF, hfin, hp, hmod, d, hflat', hdim, hcomm', hmatch'⟩

end ThreeAdicPlan
