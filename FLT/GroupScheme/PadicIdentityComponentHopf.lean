/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConnectedTensorPoint
public import FLT.GroupScheme.HenselianConnectedLocal
public import FLT.GroupScheme.PadicIdentityComponentAntipode

/-!
# The three-adic identity component is a Hopf quotient

The connected component algebra is local, and its tensor square is connected.
The counit then detects the projected comultiplication of the component
idempotent. Together with antipode stability this gives the Hopf ideal.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan.FF

attribute [local instance] threeAdicFiniteFlat_henselian threeAdicSpecialFiber_artinian

variable (X : FF ℤ_[3] ℚ_[3])

/-- The coordinate algebra of each connected component is a local ring. -/
instance componentAlgebra_isLocalRing (m : X.ComponentIndex) :
    IsLocalRing (X.ComponentAlgebra m) :=
  isLocalRing_of_henselian_idempotent_trivial (threeAdicSpecialIdeal _)
    (X.componentAlgebra_idempotent_trivial m)

/-- The tensor square of the identity component is connected. -/
theorem identityComponent_tensor_idempotent_trivial
    (d : X.ComponentAlgebra X.identityComponentIndex ⊗[ℤ_[3]]
      X.ComponentAlgebra X.identityComponentIndex) (hd : IsIdempotentElem d) :
    d = 0 ∨ d = 1 :=
  tensor_idempotent_trivial_of_local_point X.identityComponentCounit
    (X.componentAlgebra_idempotent_trivial X.identityComponentIndex) d hd

/-- Evaluating both tensor factors at the identity. -/
def identityComponentTensorCounit :
    X.ComponentAlgebra X.identityComponentIndex ⊗[ℤ_[3]]
      X.ComponentAlgebra X.identityComponentIndex →ₐ[ℤ_[3]] ℤ_[3] :=
  (Algebra.TensorProduct.lid ℤ_[3] ℤ_[3]).toAlgHom.comp
    (Algebra.TensorProduct.map X.identityComponentCounit X.identityComponentCounit)

/-- Evaluating the projected comultiplication at the two identity sections
recovers the original counit. -/
theorem identityComponentTensorCounit_comul (x : X.CoordinateRing) :
    X.identityComponentTensorCounit
      (Algebra.TensorProduct.map X.identityComponentProjection X.identityComponentProjection
        (Coalgebra.comul (R := ℤ_[3]) x)) = Coalgebra.counit (R := ℤ_[3]) x := by
  let ε := Bialgebra.counitAlgHom ℤ_[3] X.CoordinateRing
  have h : X.identityComponentTensorCounit.comp
      (Algebra.TensorProduct.map X.identityComponentProjection X.identityComponentProjection) =
      ε.comp ((Algebra.TensorProduct.lid ℤ_[3] X.CoordinateRing).toAlgHom.comp
        (Algebra.TensorProduct.map ε (AlgHom.id ℤ_[3] X.CoordinateRing))) := by
    apply AlgHom.toLinearMap_injective
    ext a b
    change X.identityComponentTensorCounit
      (X.identityComponentProjection a ⊗ₜ[ℤ_[3]] X.identityComponentProjection b) =
      ε (ε a • b)
    simp [identityComponentTensorCounit, ε]
  have hh := AlgHom.congr_fun h (Coalgebra.comul (R := ℤ_[3]) x)
  rw [AlgHom.comp_apply] at hh
  rw [hh]
  change Coalgebra.counit (R := ℤ_[3])
    (TensorProduct.lid ℤ_[3] X.CoordinateRing
      ((Coalgebra.counit (R := ℤ_[3])).rTensor X.CoordinateRing (Coalgebra.comul x))) = _
  rw [Coalgebra.rTensor_counit_comul]
  simp

/-- Comultiplication sends the identity idempotent to one after projecting both
factors to the identity component. -/
theorem identityComponentProjection_comul_idempotent :
    Algebra.TensorProduct.map X.identityComponentProjection X.identityComponentProjection
      (Coalgebra.comul (R := ℤ_[3])
        (X.connectedComponentIdempotent X.identityComponentIndex)) = 1 := by
  let d := Algebra.TensorProduct.map X.identityComponentProjection X.identityComponentProjection
    (Coalgebra.comul (R := ℤ_[3])
      (X.connectedComponentIdempotent X.identityComponentIndex))
  have hd : IsIdempotentElem d :=
    ((componentIdempotent_isIdempotent _ _).map
      (Bialgebra.comulAlgHom ℤ_[3] X.CoordinateRing).toRingHom).map
        (Algebra.TensorProduct.map X.identityComponentProjection
          X.identityComponentProjection).toRingHom
  rcases X.identityComponent_tensor_idempotent_trivial d hd with h | h
  · have hε := X.identityComponentTensorCounit_comul
      (X.connectedComponentIdempotent X.identityComponentIndex)
    change X.identityComponentTensorCounit d = _ at hε
    rw [h, map_zero, X.counit_identityComponentIdempotent] at hε
    exact (zero_ne_one hε).elim
  · exact h

/-- The identity-component ideal satisfies the comultiplication condition for
being a coideal. -/
theorem identityComponentIdeal_comul {x : X.CoordinateRing}
    (hx : x ∈ X.identityComponentIdeal) :
    TensorProduct.map X.identityComponentProjection.toLinearMap
      X.identityComponentProjection.toLinearMap (Coalgebra.comul (R := ℤ_[3]) x) = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
  change Algebra.TensorProduct.map X.identityComponentProjection X.identityComponentProjection
    ((Bialgebra.comulAlgHom ℤ_[3] X.CoordinateRing)
      ((1 - X.connectedComponentIdempotent X.identityComponentIndex) * a)) = 0
  rw [map_mul, map_sub, map_one, map_mul, map_sub, map_one]
  change (1 - Algebra.TensorProduct.map X.identityComponentProjection X.identityComponentProjection
    (Coalgebra.comul (R := ℤ_[3])
      (X.connectedComponentIdempotent X.identityComponentIndex))) * _ = 0
  rw [X.identityComponentProjection_comul_idempotent, sub_self, zero_mul]

/-- The identity component is cut out by a Hopf ideal. -/
instance identityComponentIdeal_isHopfIdeal : X.identityComponentIdeal.IsHopfIdeal ℤ_[3] where
  counit_eq_zero := fun {_} hx ↦ X.identityComponentIdeal_counit hx
  map_mkQ_comul_eq_zero := fun {_} hx ↦ X.identityComponentIdeal_comul hx
  antipode_mem := fun {_} hx ↦ X.identityComponentIdeal_antipode hx

/-- The identity component inherits its Hopf structure from the specified quotient. -/
instance identityComponentHopfAlgebra :
    HopfAlgebra ℤ_[3] (X.ComponentAlgebra X.identityComponentIndex) :=
  inferInstanceAs (HopfAlgebra ℤ_[3] (X.CoordinateRing ⧸ X.identityComponentIdeal))

/-- The identity-component inclusion, contravariantly on coordinate Hopf algebras. -/
def identityComponentBialgHom : X.CoordinateRing →ₐc[ℤ_[3]]
    X.ComponentAlgebra X.identityComponentIndex :=
  Bialgebra.Quotient.mkBialgHom X.identityComponentIdeal

/-- The inclusion is a closed immersion: its coordinate homomorphism is surjective. -/
theorem identityComponentBialgHom_surjective : Function.Surjective X.identityComponentBialgHom :=
  Ideal.Quotient.mk_surjective

end ThreeAdicPlan.FF
