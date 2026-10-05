/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalUnramifiedTwistGroupPoints
public import FLT.GaloisRepresentation.Extensions.OrdinaryFiltrationTwist
public import FLT.GaloisRepresentation.Extensions.OrdinaryFiltrationTransport
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Coefficients and ordinary filtrations on the actual finite-flat twist

The original coefficient module transports through the proved additive point
comparison. Its Galois action is the inverse-character scalar twist, so the
original ordinary filtration transports to this actual finite-flat model.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NumberField IsLocalRing GaloisRepresentation.Extensions LocalRamification
open SemilinearDescent
open scoped TensorProduct
namespace ThreeAdicPlan

variable {K k : Type} [Field K] [NumberField K] [Field k]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K)]
  (p : ℕ) [Fact p.Prime] [CharP k p]
  [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  (X : FF (v.adicCompletionIntegers K) (v.adicCompletion K)) [Module k X.Points]
  [SMulCommClass k (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) X.Points]
  (he : RaynaudParameters.order (p : v.adicCompletionIntegers K) < p - 1)
  [TopologicalSpace k] [DiscreteTopology k]
  (χ : Field.absoluteGaloisGroup (v.adicCompletion K) →* kˣ) (hc : Continuous χ)
local notation "O" => v.adicCompletionIntegers K
local notation "Kv" => v.adicCompletion K
local notation "L" => openNormalFixedField (characterOpenNormal v χ hc)
local notation "D" => IntegralClosure O L
local notation "σ" => MulSemiringAction.toAlgAut Gal(L/Kv) O D

local notation "τ" => localUnramifiedTwistAction v p X he χ hc

variable (hχ : localInertiaGroup v ≤ χ.ker)

local notation "Y" => localUnramifiedTwistModel v p X he χ hc hχ
local notation "e" => localUnramifiedTwistPointAddEquiv v p X he χ hc hχ

/-- Transport the original coefficient module to the actual twisted model's points. -/
@[instance_reducible]
def localUnramifiedTwistModule : Module k (Y).Points := (e).symm.module k

/-- The actual point comparison is linear for the transported original coefficients. -/
def localUnramifiedTwistLinearEquiv :
    letI := localUnramifiedTwistModule v p X he χ hc hχ
    X.Points ≃ₗ[k] (Y).Points := ((e).symm.linearEquiv k).symm

local instance : SMulCommClass (Field.absoluteGaloisGroup Kv) k X.Points :=
  SMulCommClass.symm _ _ _

/-- Galois automorphisms commute with the transported coefficient action. -/
theorem localUnramifiedTwistSMulComm :
    letI := localUnramifiedTwistModule v p X he χ hc hχ
    SMulCommClass (Field.absoluteGaloisGroup Kv) k (Y).Points := by
  let := localUnramifiedTwistModule v p X he χ hc hχ
  let l := localUnramifiedTwistLinearEquiv v p X he χ hc hχ
  constructor
  intro g a y
  obtain ⟨x, rfl⟩ := (e).surjective y
  change g • (a • l x) = a • (g • l x)
  rw [← l.map_smul]
  change g • e (a • x) = a • (g • e x)
  rw [localUnramifiedTwistPointAddEquiv_equivariant,
    localUnramifiedTwistPointAddEquiv_equivariant]
  change l ((↑(χ g)⁻¹ : k) • (g • (a • x))) = a • l ((↑(χ g)⁻¹ : k) • (g • x))
  rw [smul_comm g a, smul_comm (↑(χ g)⁻¹ : k) a, l.map_smul]

variable {α β : (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
  AlgebraicClosure (v.adicCompletion K)) →* kˣ}
  (E : OrdinaryFiltration (Representation.ofDistribMulAction k
    (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K)) X.Points) α β)

/-- The original ordinary filtration, twisted on both lines, on the actual integral model. -/
def localUnramifiedTwistFiltration :
    letI := localUnramifiedTwistModule v p X he χ hc hχ
    letI := localUnramifiedTwistSMulComm v p X he χ hc hχ
    OrdinaryFiltration
      (Representation.ofDistribMulAction k (Field.absoluteGaloisGroup Kv) (Y).Points)
      (α * χ⁻¹) (β * χ⁻¹) := by
  letI := localUnramifiedTwistModule v p X he χ hc hχ
  letI := localUnramifiedTwistSMulComm v p X he χ hc hχ
  exact (E.twist χ⁻¹).transport (localUnramifiedTwistLinearEquiv v p X he χ hc hχ)
    (fun g x ↦ localUnramifiedTwistPointAddEquiv_equivariant v p X he χ hc hχ g x)

end ThreeAdicPlan
