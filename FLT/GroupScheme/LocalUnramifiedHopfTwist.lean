/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalUnramifiedScalarTwist
public import FLT.AbsoluteGaloisGroup.UnramifiedCharacterHopfComparison
public import FLT.GroupScheme.FiniteFlatScalarExtension

/-!
# The finite-flat unramified twist of the original local model

The existing fixed algebra now carries its descended Hopf structure and is
packaged as a finite-flat model. Its coefficient action is the one constructed
from the original scalar action, with no supplied descent or Hopf-law fields.
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

/-- The original integral scalar action is Hopf compatible at every splitting automorphism. -/
theorem localUnramifiedTwistAction_hopf (g : Gal(L/Kv)) :
    ∃ f : X.CoordinateRing →ₐc[O] X.CoordinateRing, f.toAlgHom = (τ g).toAlgHom :=
  ⟨localIntegralScalar v p X he (finiteModelCharacter v χ hc g : k), rfl⟩

variable (hχ : localInertiaGroup v ≤ χ.ker)

/-- Hopf structure on the actual fixed coordinates of the specified local model. -/
@[instance_reducible]
def localUnramifiedTwistHopf : HopfAlgebra O (twistModel σ τ) :=
  finiteCharacterTwistHopf v χ hc X.CoordinateRing τ
    (localUnramifiedTwistAction_hopf v p X he χ hc) hχ

/-- The actual fixed Hopf coordinates define a finite-flat model over the original base. -/
def localUnramifiedTwistModel : FF O Kv := by
  letI := localUnramifiedTwistHopf v p X he χ hc hχ
  letI := finiteCharacterTwistIsCocomm v χ hc X.CoordinateRing τ
    (localUnramifiedTwistAction_hopf v p X he χ hc) hχ
  let hf := localUnramifiedTwist_finite_free v p X he χ hc
  let : Module.Finite O (twistModel σ τ) := hf.1
  let : Module.Free O (twistModel σ τ) := hf.2
  let : Module.Flat O (twistModel σ τ) := Module.Flat.of_free
  let : HopfAlgebra.IsFiniteFlat O (twistModel σ τ) := ⟨⟩
  let := localUnramifiedTwist_generic_etale v p X he χ hc hχ
  let := HopfAlgebra.pointsCommGroup Kv (AlgebraicClosure Kv) (Kv ⊗[O] twistModel σ τ)
  exact
    { CoordinateRing := twistModel σ τ
      Points := Additive (Kv ⊗[O] twistModel σ τ →ₐ[Kv] AlgebraicClosure Kv)
      points :=
        { toFun := id
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      points_bijective := Function.bijective_id }

/-- The finite-flat model uses exactly the original invariant subalgebra. -/
theorem localUnramifiedTwistModel_coordinates :
    (localUnramifiedTwistModel v p X he χ hc hχ).CoordinateRing = twistModel σ τ := rfl

end ThreeAdicPlan
