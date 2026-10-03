/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudDescentActionAgreement
public import FLT.GroupScheme.RaynaudInertiaScalarFiltration

/-!
# Constructed scalar filtrations over the finite unramified descent field

The original finite continuous point action supplies the inertia representation.
Normal descent proves agreement with the actual base-changed Galois action;
cardinality induction then constructs all scalar factors and their models.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open NumberField IsLocalRing

variable {K : Type} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "I" => localInertiaGroup v

variable (X : FF (v.adicCompletionIntegers K) (v.adicCompletion K))
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  [Module (ZMod p) X.Points]

local notation "L₀" => InertiaDescent.field (X := X.Points) I
local notation "S₀" => IntegralClosure O L₀

/-- The actual finite unramified base change has a constructed scalar filtration. -/
theorem exists_scalarFiltration_inertiaDescent :
    ∃ n, (X.restrictedScalarExtension S₀ L₀).HasScalarFiltration p n := by
  let : Module (ZMod p) (X.restrictedScalarExtension S₀ L₀).Points :=
    inferInstanceAs (Module (ZMod p) X.Points)
  let ρ : Representation (ZMod p) I (X.restrictedScalarExtension S₀ L₀).Points :=
    (X.primeRepresentation p).comp (localInertiaGroup v).subtype
  have hρ : ρ.IsDiscreteContinuous := by
    intro x y
    exact (ContinuousSMulDiscrete.isOpen_smul_eq (M := X.Points)
      (AlgebraicClosure Kv ≃ₐ[Kv] AlgebraicClosure Kv) (x : X.Points) (y : X.Points)).preimage
        continuous_subtype_val
  apply exists_scalarFiltration_of_inertia_agreement v p (X.restrictedScalarExtension S₀ L₀) ρ hρ
  intro σ
  exact InertiaDescent.exists_inertia_action_map (X := X.Points) I σ

end ThreeAdicPlan
