/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalIdentityComponent

/-! # Inversion on the original rational-place identity component -/

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

/-- The ideal cutting out the component containing the identity. -/
def rationalIdentityComponentIdeal : Ideal X.CoordinateRing :=
  Ideal.span {1 - X.rationalComponentIdempotent X.rationalIdentityComponentIndex}

/-- The quotient map to the identity component's coordinate algebra. -/
abbrev rationalIdentityComponentProjection :
    X.CoordinateRing →ₐ[O] X.RationalComponentAlgebra X.rationalIdentityComponentIndex :=
  Ideal.Quotient.mkₐ O X.rationalIdentityComponentIdeal

/-- The component counit agrees with the original counit on representatives. -/
@[simp] theorem rationalIdentityComponentCounit_projection (x : X.CoordinateRing) :
    X.rationalIdentityComponentCounit (X.rationalIdentityComponentProjection x) =
      Coalgebra.counit (R := O) x := rfl

/-- An idempotent in the identity component is determined by its counit. -/
theorem rationalIdentityComponent_idempotent_eq_one
    {d : X.RationalComponentAlgebra X.rationalIdentityComponentIndex} (hd :
      IsIdempotentElem d)
    (hε : X.rationalIdentityComponentCounit d = 1) : d = 1 := by
  rcases X.rationalComponentAlgebra_idempotent_trivial X.rationalIdentityComponentIndex d
    hd with h | h
  · rw [h, map_zero] at hε
    exact (zero_ne_one hε).elim
  · exact h

/-- The component idempotent becomes one in the identity component. -/
@[simp] theorem rationalIdentityComponentProjection_idempotent :
    X.rationalIdentityComponentProjection
      (X.rationalComponentIdempotent X.rationalIdentityComponentIndex) = 1 := by
  apply X.rationalIdentityComponent_idempotent_eq_one
  · exact (componentIdempotent_isIdempotent _ _).map
      X.rationalIdentityComponentProjection.toRingHom
  · exact X.counit_rationalIdentityComponentIdempotent

/-- Inversion sends the identity-component idempotent to one after projection. -/
@[simp] theorem rationalIdentityComponentProjection_antipode_idempotent :
    X.rationalIdentityComponentProjection (HopfAlgebra.antipode O
      (X.rationalComponentIdempotent X.rationalIdentityComponentIndex)) = 1 := by
  apply X.rationalIdentityComponent_idempotent_eq_one
  · exact ((componentIdempotent_isIdempotent _ _).map
      (HopfAlgebra.antipodeAlgHom O X.CoordinateRing).toRingHom).map
        X.rationalIdentityComponentProjection.toRingHom
  · rw [X.rationalIdentityComponentCounit_projection, HopfAlgebra.counit_antipode,
      X.counit_rationalIdentityComponentIdempotent]

/-- The identity-component ideal is killed by the counit. -/
theorem rationalIdentityComponentIdeal_counit {x : X.CoordinateRing}
    (hx : x ∈ X.rationalIdentityComponentIdeal) : Coalgebra.counit (R := O) x = 0 := by
  rw [← X.rationalIdentityComponentCounit_projection]
  have hq : X.rationalIdentityComponentProjection x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  rw [hq, map_zero]

/-- The identity-component ideal is stable under the antipode. -/
theorem rationalIdentityComponentIdeal_antipode {x : X.CoordinateRing}
    (hx : x ∈ X.rationalIdentityComponentIdeal) :
    HopfAlgebra.antipode O x ∈ X.rationalIdentityComponentIdeal := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change X.rationalIdentityComponentProjection ((HopfAlgebra.antipodeAlgHom O
    X.CoordinateRing) ((1 - X.rationalComponentIdempotent
      X.rationalIdentityComponentIndex) * a)) = 0
  rw [map_mul, map_sub, map_one, map_mul, map_sub, map_one]
  change (1 - X.rationalIdentityComponentProjection (HopfAlgebra.antipode O
    (X.rationalComponentIdempotent X.rationalIdentityComponentIndex))) * _ = 0
  rw [X.rationalIdentityComponentProjection_antipode_idempotent, sub_self, zero_mul]
end ThreeAdicPlan.FF
