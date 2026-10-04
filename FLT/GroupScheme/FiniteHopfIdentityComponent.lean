/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteHopfIdentityAntipode
public import FLT.GroupScheme.ConnectedTensorPoint

/-! # The identity local factor of a finite Hopf algebra is a Hopf quotient -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace HopfAlgebra

variable (k A : Type*) [Field k] [CommRing A] [HopfAlgebra k A]
  [IsArtinianRing A] [Module.Finite k A]

/-- The tensor square of the identity local factor is connected. -/
theorem finiteIdentity_tensor_idempotent_trivial
    (d : FiniteIdentityComponent k A ⊗[k] FiniteIdentityComponent k A)
    (hd : IsIdempotentElem d) : d = 0 ∨ d = 1 :=
  ThreeAdicPlan.tensor_idempotent_trivial_of_local_point (finiteIdentityCounit k A)
    (FiniteAlgebra.component_idempotent_trivial A _) d hd

/-- Evaluation at the two identity points. -/
def finiteIdentityTensorCounit :
    FiniteIdentityComponent k A ⊗[k] FiniteIdentityComponent k A →ₐ[k] k :=
  (Algebra.TensorProduct.lid k k).toAlgHom.comp
    (Algebra.TensorProduct.map (finiteIdentityCounit k A) (finiteIdentityCounit k A))

omit [Module.Finite k A] in
/-- The original counit identity survives projection to both local factors. -/
theorem finiteIdentityTensorCounit_comul (x : A) :
    finiteIdentityTensorCounit k A
      (Algebra.TensorProduct.map (finiteIdentityProjection k A) (finiteIdentityProjection k A)
        (Coalgebra.comul (R := k) x)) = Coalgebra.counit (R := k) x := by
  let ε := Bialgebra.counitAlgHom k A
  have h : (finiteIdentityTensorCounit k A).comp
      (Algebra.TensorProduct.map (finiteIdentityProjection k A) (finiteIdentityProjection k A)) =
      ε.comp ((Algebra.TensorProduct.lid k A).toAlgHom.comp
        (Algebra.TensorProduct.map ε (AlgHom.id k A))) := by
    apply AlgHom.toLinearMap_injective
    ext a b
    change finiteIdentityTensorCounit k A
      (finiteIdentityProjection k A a ⊗ₜ[k] finiteIdentityProjection k A b) = ε (ε a • b)
    simp [finiteIdentityTensorCounit, ε]
  have hh := AlgHom.congr_fun h (Coalgebra.comul (R := k) x)
  rw [AlgHom.comp_apply] at hh
  rw [hh]
  change Coalgebra.counit (R := k)
    (TensorProduct.lid k A ((Coalgebra.counit (R := k)).rTensor A (Coalgebra.comul x))) = _
  rw [Coalgebra.rTensor_counit_comul]
  simp

/-- Projected comultiplication carries the identity idempotent to one. -/
theorem finiteIdentityProjection_comul_idempotent :
    Algebra.TensorProduct.map (finiteIdentityProjection k A) (finiteIdentityProjection k A)
      (Coalgebra.comul (R := k) (finiteIdentityIdempotent k A)) = 1 := by
  let d := Algebra.TensorProduct.map (finiteIdentityProjection k A) (finiteIdentityProjection k A)
    (Coalgebra.comul (R := k) (finiteIdentityIdempotent k A))
  have hd : IsIdempotentElem d :=
    ((finiteIdentityIdempotent_isIdempotent k A).map (Bialgebra.comulAlgHom k A).toRingHom).map
      (Algebra.TensorProduct.map (finiteIdentityProjection k A)
        (finiteIdentityProjection k A)).toRingHom
  rcases finiteIdentity_tensor_idempotent_trivial k A d hd with h | h
  · have hε := finiteIdentityTensorCounit_comul k A (finiteIdentityIdempotent k A)
    change finiteIdentityTensorCounit k A d = _ at hε
    rw [h, map_zero, counit_finiteIdentityIdempotent] at hε
    exact (zero_ne_one hε).elim
  · exact h

/-- Comultiplication kills the defining ideal after projecting both tensor factors. -/
theorem finiteIdentityIdeal_comul {x : A} (hx : x ∈ finiteIdentityIdeal k A) :
    TensorProduct.map (finiteIdentityProjection k A).toLinearMap
      (finiteIdentityProjection k A).toLinearMap (Coalgebra.comul (R := k) x) = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
  change Algebra.TensorProduct.map (finiteIdentityProjection k A) (finiteIdentityProjection k A)
    ((Bialgebra.comulAlgHom k A) ((1 - finiteIdentityIdempotent k A) * a)) = 0
  rw [map_mul, map_sub, map_one, map_mul, map_sub, map_one]
  change (1 - Algebra.TensorProduct.map (finiteIdentityProjection k A)
    (finiteIdentityProjection k A)
    (Coalgebra.comul (R := k) (finiteIdentityIdempotent k A))) * _ = 0
  rw [finiteIdentityProjection_comul_idempotent, sub_self, zero_mul]

/-- The identity component is defined by a Hopf ideal. -/
instance finiteIdentityIdeal_isHopfIdeal : (finiteIdentityIdeal k A).IsHopfIdeal k where
  counit_eq_zero := fun {_} hx ↦ finiteIdentityIdeal_counit k A hx
  map_mkQ_comul_eq_zero := fun {_} hx ↦ finiteIdentityIdeal_comul k A hx
  antipode_mem := fun {_} hx ↦ finiteIdentityIdeal_antipode k A hx

/-- The induced Hopf structure on the local quotient. -/
instance finiteIdentityComponentHopfAlgebra : HopfAlgebra k (FiniteIdentityComponent k A) :=
  inferInstanceAs (HopfAlgebra k (A ⧸ finiteIdentityIdeal k A))

/-- The original quotient map, preserving comultiplication and counit. -/
def finiteIdentityBialgHom : A →ₐc[k] FiniteIdentityComponent k A :=
  Bialgebra.Quotient.mkBialgHom (finiteIdentityIdeal k A)

/-- The identity factor is a closed subgroup of the original finite group scheme. -/
theorem finiteIdentityBialgHom_surjective : Function.Surjective (finiteIdentityBialgHom k A) :=
  Ideal.Quotient.mk_surjective

end HopfAlgebra
