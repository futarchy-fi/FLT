/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudInertiaSimpleScalars
public import FLT.GroupScheme.RaynaudExtension
public import FLT.AbsoluteGaloisGroup.InertiaDescentField

/-!
# Descent of the constructed simple-factor scalar action

An actual inertia subquotient acquires a finite-flat model over the finite
unramified descent ring. Its constructed rank-one scalar action commutes
with the descended Galois action, by descent of each scalar endomorphism.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open NumberField IsLocalRing

variable {K : Type} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ω" => AlgebraicClosure Kv
local notation "I" => localInertiaGroup v

variable (X : FF (v.adicCompletionIntegers K) (v.adicCompletion K))
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  {U W : Type} [AddCommGroup U] [AddCommGroup W]
  [DistribMulAction (localInertiaGroup v) U] [DistribMulAction (localInertiaGroup v) W]
  [Module (ZMod p) W]
  (ρ : Representation (ZMod p) (localInertiaGroup v) W) [ρ.IsIrreducible]
  [TopologicalSpace (Module.End (ZMod p) W)ˣ]
  [DiscreteTopology (Module.End (ZMod p) W)ˣ]

local notation "L₀" => InertiaDescent.field (X := X.Points) I
local notation "S₀" => IntegralClosure O L₀

/-- Actual simple inertia factors descend with a derived commuting rank-one scalar action. -/
theorem exists_simple_factor_scalar_descent
    (hρ : Continuous ρ.toHomUnits) (hact : ∀ σ w, ρ σ w = σ • w)
    (i : U →+[I] X.Points) (q : U →+[I] W)
    (hi : Function.Injective i) (hq : Function.Surjective q) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F p) (_ : Module F W)
      (dU : DistribMulAction (Ω ≃ₐ[L₀] Ω) U) (dW : DistribMulAction (Ω ≃ₐ[L₀] Ω) W),
      let := dU; letI := dW
      GaloisModule.IsFiniteFlat S₀ L₀ Ω W ∧ Module.finrank F W = 1 ∧
      SMulCommClass F (Ω ≃ₐ[L₀] Ω) W ∧
      (∀ (σ : Ω ≃ₐ[L₀] Ω) (t : I),
        (∀ x : X.Points, (σ.restrictScalars Kv) • x = t.1 • x) →
        ∀ w : W, σ • w = t • w) := by
  let : Finite U := Finite.of_injective i hi
  let : Finite W := Finite.of_surjective q hq
  obtain ⟨F, hF, hfin, hp, hmod, hdim, hs⟩ :=
    LocalRamification.exists_rank_one_scalar_field_of_local_inertia v p ρ hρ
  obtain ⟨dU, dW, hflat, _, hmatch, hend⟩ :=
    @InertiaDescent.subquotient_model Kv X.Points _ _ _ _ _ _ I O S₀ U W
      _ _ _ _ _ (IsScalarTower.of_algebraMap_eq' rfl) _ _ _ _ _ _ X.isFiniteFlat i q hi hq
  let := dU
  let := dW
  refine ⟨F, hF, hfin, hp, hmod, dU, dW, hflat, hdim, ?_, hmatch⟩
  constructor
  intro a σ w
  let f : W →+[I] W := {
    toFun := fun w ↦ a • w
    map_zero' := smul_zero a
    map_add' := smul_add a
    map_smul' := fun τ w ↦ by simpa only [hact, MonoidHom.id_apply] using (hs a τ w).symm }
  exact hend f σ w

end ThreeAdicPlan
