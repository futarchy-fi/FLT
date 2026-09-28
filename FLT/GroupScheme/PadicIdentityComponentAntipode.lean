/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PadicConnectedComponents

/-!
# Inversion preserves the three-adic identity component

The component counit detects its idempotents. Applying this observation to the
antipode proves stability of the defining ideal under inversion.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan.FF

attribute [local instance] threeAdicFiniteFlat_henselian threeAdicSpecialFiber_artinian

variable (X : FF ℤ_[3] ℚ_[3])

/-- The ideal cutting out the component containing the identity. -/
def identityComponentIdeal : Ideal X.CoordinateRing :=
  Ideal.span {1 - X.connectedComponentIdempotent X.identityComponentIndex}

/-- The quotient map to the identity component's coordinate algebra. -/
abbrev identityComponentProjection :
    X.CoordinateRing →ₐ[ℤ_[3]] X.ComponentAlgebra X.identityComponentIndex :=
  Ideal.Quotient.mkₐ ℤ_[3] X.identityComponentIdeal

/-- The component counit agrees with the original counit on representatives. -/
@[simp] theorem identityComponentCounit_projection (x : X.CoordinateRing) :
    X.identityComponentCounit (X.identityComponentProjection x) =
      Coalgebra.counit (R := ℤ_[3]) x := rfl

/-- An idempotent in the identity component is determined by its counit. -/
theorem identityComponent_idempotent_eq_one
    {d : X.ComponentAlgebra X.identityComponentIndex} (hd : IsIdempotentElem d)
    (hε : X.identityComponentCounit d = 1) : d = 1 := by
  rcases X.componentAlgebra_idempotent_trivial X.identityComponentIndex d hd with h | h
  · rw [h, map_zero] at hε
    exact (zero_ne_one hε).elim
  · exact h

/-- The component idempotent becomes one in the identity component. -/
@[simp] theorem identityComponentProjection_idempotent :
    X.identityComponentProjection
      (X.connectedComponentIdempotent X.identityComponentIndex) = 1 := by
  apply X.identityComponent_idempotent_eq_one
  · exact (componentIdempotent_isIdempotent _ _).map
      X.identityComponentProjection.toRingHom
  · exact X.counit_identityComponentIdempotent

/-- Inversion sends the identity-component idempotent to one after projection. -/
@[simp] theorem identityComponentProjection_antipode_idempotent :
    X.identityComponentProjection (HopfAlgebra.antipode ℤ_[3]
      (X.connectedComponentIdempotent X.identityComponentIndex)) = 1 := by
  apply X.identityComponent_idempotent_eq_one
  · exact ((componentIdempotent_isIdempotent _ _).map
      (HopfAlgebra.antipodeAlgHom ℤ_[3] X.CoordinateRing).toRingHom).map
        X.identityComponentProjection.toRingHom
  · rw [X.identityComponentCounit_projection, HopfAlgebra.counit_antipode,
      X.counit_identityComponentIdempotent]

/-- The identity-component ideal is killed by the counit. -/
theorem identityComponentIdeal_counit {x : X.CoordinateRing}
    (hx : x ∈ X.identityComponentIdeal) : Coalgebra.counit (R := ℤ_[3]) x = 0 := by
  rw [← X.identityComponentCounit_projection]
  have hq : X.identityComponentProjection x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  rw [hq, map_zero]

/-- The identity-component ideal is stable under the antipode. -/
theorem identityComponentIdeal_antipode {x : X.CoordinateRing}
    (hx : x ∈ X.identityComponentIdeal) :
    HopfAlgebra.antipode ℤ_[3] x ∈ X.identityComponentIdeal := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change X.identityComponentProjection ((HopfAlgebra.antipodeAlgHom ℤ_[3]
    X.CoordinateRing) ((1 - X.connectedComponentIdempotent X.identityComponentIndex) * a)) = 0
  rw [map_mul, map_sub, map_one, map_mul, map_sub, map_one]
  change (1 - X.identityComponentProjection (HopfAlgebra.antipode ℤ_[3]
    (X.connectedComponentIdempotent X.identityComponentIndex))) * _ = 0
  rw [X.identityComponentProjection_antipode_idempotent, sub_self, zero_mul]

end ThreeAdicPlan.FF
