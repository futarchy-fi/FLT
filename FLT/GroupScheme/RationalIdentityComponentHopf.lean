/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalIdentityComponentAntipode
public import FLT.GroupScheme.HenselianConnectedLocal
public import FLT.GroupScheme.ConnectedTensorPoint

/-! # The original rational-place identity component is a Hopf quotient -/

@[expose] public noncomputable section
open scoped TensorProduct
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.FF
attribute [local instance] rationalFiniteFlat_henselian rationalSpecialFiber_artinian
variable {p : ℕ} [Fact p.Prime]
  (X : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ))
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)

/-- The coordinate algebra of each connected component is a local ring. -/
instance rationalComponentAlgebra_isLocalRing (m : X.RationalComponentIndex) :
    IsLocalRing (X.RationalComponentAlgebra m) :=
  isLocalRing_of_henselian_idempotent_trivial (rationalSpecialIdeal p _)
    (X.rationalComponentAlgebra_idempotent_trivial m)

/-- The tensor square of the identity component is connected. -/
theorem rationalIdentityComponent_tensor_idempotent_trivial
    (d : X.RationalComponentAlgebra X.rationalIdentityComponentIndex ⊗[O]
      X.RationalComponentAlgebra X.rationalIdentityComponentIndex) (hd : IsIdempotentElem
        d) :
    d = 0 ∨ d = 1 :=
  tensor_idempotent_trivial_of_local_point X.rationalIdentityComponentCounit
    (X.rationalComponentAlgebra_idempotent_trivial X.rationalIdentityComponentIndex) d hd

/-- Evaluating both tensor factors at the identity. -/
def rationalIdentityComponentTensorCounit :
    X.RationalComponentAlgebra X.rationalIdentityComponentIndex ⊗[O]
      X.RationalComponentAlgebra X.rationalIdentityComponentIndex →ₐ[O] O :=
  (Algebra.TensorProduct.lid O O).toAlgHom.comp
    (Algebra.TensorProduct.map X.rationalIdentityComponentCounit X.rationalIdentityComponentCounit)

/-- Evaluating the projected comultiplication at the two identity sections
recovers the original counit. -/
theorem rationalIdentityComponentTensorCounit_comul (x : X.CoordinateRing) :
    X.rationalIdentityComponentTensorCounit
      (Algebra.TensorProduct.map X.rationalIdentityComponentProjection
        X.rationalIdentityComponentProjection
        (Coalgebra.comul (R := O) x)) = Coalgebra.counit (R := O) x := by
  let ε := Bialgebra.counitAlgHom O X.CoordinateRing
  have h : X.rationalIdentityComponentTensorCounit.comp
      (Algebra.TensorProduct.map X.rationalIdentityComponentProjection
        X.rationalIdentityComponentProjection) =
      ε.comp ((Algebra.TensorProduct.lid O X.CoordinateRing).toAlgHom.comp
        (Algebra.TensorProduct.map ε (AlgHom.id O X.CoordinateRing))) := by
    apply AlgHom.toLinearMap_injective
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    change X.rationalIdentityComponentTensorCounit
      (X.rationalIdentityComponentProjection a ⊗ₜ[O] X.rationalIdentityComponentProjection b) =
      ε (ε a • b)
    simp [rationalIdentityComponentTensorCounit, ε]
  have hh := AlgHom.congr_fun h (Coalgebra.comul (R := O) x)
  rw [AlgHom.comp_apply] at hh
  rw [hh]
  change Coalgebra.counit (R := O)
    (TensorProduct.lid O X.CoordinateRing
      ((Coalgebra.counit (R := O)).rTensor X.CoordinateRing (Coalgebra.comul x))) = _
  rw [Coalgebra.rTensor_counit_comul]
  simp

/-- Comultiplication sends the identity idempotent to one after projecting both
factors to the identity component. -/
theorem rationalIdentityComponentProjection_comul_idempotent :
    Algebra.TensorProduct.map X.rationalIdentityComponentProjection
      X.rationalIdentityComponentProjection
      (Coalgebra.comul (R := O)
        (X.rationalComponentIdempotent X.rationalIdentityComponentIndex)) = 1 := by
  let d := Algebra.TensorProduct.map X.rationalIdentityComponentProjection
    X.rationalIdentityComponentProjection
    (Coalgebra.comul (R := O)
      (X.rationalComponentIdempotent X.rationalIdentityComponentIndex))
  have hd : IsIdempotentElem d :=
    ((componentIdempotent_isIdempotent _ _).map
      (Bialgebra.comulAlgHom O X.CoordinateRing).toRingHom).map
        (Algebra.TensorProduct.map X.rationalIdentityComponentProjection
          X.rationalIdentityComponentProjection).toRingHom
  rcases X.rationalIdentityComponent_tensor_idempotent_trivial d hd with h | h
  · have hε := X.rationalIdentityComponentTensorCounit_comul
      (X.rationalComponentIdempotent X.rationalIdentityComponentIndex)
    change X.rationalIdentityComponentTensorCounit d = _ at hε
    rw [h, map_zero, X.counit_rationalIdentityComponentIdempotent] at hε
    exact (zero_ne_one hε).elim
  · exact h

/-- The identity-component ideal satisfies the comultiplication condition for
being a coideal. -/
theorem rationalIdentityComponentIdeal_comul {x : X.CoordinateRing}
    (hx : x ∈ X.rationalIdentityComponentIdeal) :
    TensorProduct.map X.rationalIdentityComponentProjection.toLinearMap
      X.rationalIdentityComponentProjection.toLinearMap (Coalgebra.comul (R := O) x) = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
  change Algebra.TensorProduct.map X.rationalIdentityComponentProjection
    X.rationalIdentityComponentProjection
    ((Bialgebra.comulAlgHom O X.CoordinateRing)
      ((1 - X.rationalComponentIdempotent X.rationalIdentityComponentIndex) * a)) = 0
  rw [map_mul, map_sub, map_one, map_mul, map_sub, map_one]
  change (1 - Algebra.TensorProduct.map X.rationalIdentityComponentProjection
    X.rationalIdentityComponentProjection
    (Coalgebra.comul (R := O)
      (X.rationalComponentIdempotent X.rationalIdentityComponentIndex))) * _ = 0
  rw [X.rationalIdentityComponentProjection_comul_idempotent, sub_self, zero_mul]

/-- The identity component is cut out by a Hopf ideal. -/
instance rationalIdentityComponentIdeal_isHopfIdeal :
  X.rationalIdentityComponentIdeal.IsHopfIdeal O where
  counit_eq_zero := fun {_} hx ↦ X.rationalIdentityComponentIdeal_counit hx
  map_mkQ_comul_eq_zero := fun {_} hx ↦ X.rationalIdentityComponentIdeal_comul hx
  antipode_mem := fun {_} hx ↦ X.rationalIdentityComponentIdeal_antipode hx

/-- The identity component inherits its Hopf structure from the specified quotient. -/
instance rationalIdentityComponentHopfAlgebra :
    HopfAlgebra O (X.RationalComponentAlgebra X.rationalIdentityComponentIndex) :=
  inferInstanceAs (HopfAlgebra O (X.CoordinateRing ⧸ X.rationalIdentityComponentIdeal))

/-- The identity-component inclusion, contravariantly on coordinate Hopf algebras. -/
def rationalIdentityComponentBialgHom : X.CoordinateRing →ₐc[O]
    X.RationalComponentAlgebra X.rationalIdentityComponentIndex :=
  Bialgebra.Quotient.mkBialgHom X.rationalIdentityComponentIdeal

/-- The inclusion is a closed immersion: its coordinate homomorphism is surjective. -/
theorem rationalIdentityComponentBialgHom_surjective : Function.Surjective
  X.rationalIdentityComponentBialgHom :=
  Ideal.Quotient.mk_surjective
end ThreeAdicPlan.FF
