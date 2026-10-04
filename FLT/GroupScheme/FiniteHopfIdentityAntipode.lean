/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteAlgebraPointComponent
public import Mathlib.RingTheory.HopfAlgebra.Quotient

/-! # The identity local factor and its stability under inversion -/

@[expose] public noncomputable section

namespace HopfAlgebra

open FiniteAlgebra

variable (k A : Type*) [Field k] [CommRing A] [HopfAlgebra k A]
  [IsArtinianRing A]

/-- The primitive idempotent selected by the original counit. -/
def finiteIdentityIdempotent : A := componentIdempotent A
  (pointComponentIndex (Bialgebra.counitAlgHom k A))

/-- The ideal cutting out the identity local factor. -/
abbrev finiteIdentityIdeal : Ideal A := pointComponentIdeal (Bialgebra.counitAlgHom k A)

/-- The actual quotient coordinate algebra of the identity factor. -/
abbrev FiniteIdentityComponent := A ⧸ finiteIdentityIdeal k A

/-- Projection from the original coordinate algebra. -/
abbrev finiteIdentityProjection : A →ₐ[k] FiniteIdentityComponent k A :=
  Ideal.Quotient.mkₐ k _

/-- The restricted identity point. -/
def finiteIdentityCounit : FiniteIdentityComponent k A →ₐ[k] k :=
  componentPoint (Bialgebra.counitAlgHom k A)

instance finiteIdentityComponent_finite [Module.Finite k A] :
    Module.Finite k (FiniteIdentityComponent k A) :=
  Module.Finite.of_surjective (finiteIdentityProjection k A).toLinearMap
    Ideal.Quotient.mk_surjective

instance finiteIdentityComponent_isLocalRing : IsLocalRing (FiniteIdentityComponent k A) :=
  inferInstanceAs (IsLocalRing (Component A (pointComponentIndex (Bialgebra.counitAlgHom k A))))

/-- The restricted counit agrees with the original counit on representatives. -/
theorem finiteIdentityCounit_projection (x : A) :
    finiteIdentityCounit k A (finiteIdentityProjection k A x) =
      Coalgebra.counit (R := k) x := rfl

@[simp]
theorem finiteIdentityCounit_mk (x : A) :
    finiteIdentityCounit k A (Ideal.Quotient.mk (finiteIdentityIdeal k A) x) =
      Coalgebra.counit (R := k) x := rfl

@[simp]
theorem counit_finiteIdentityIdempotent :
    Coalgebra.counit (R := k) (finiteIdentityIdempotent k A) = 1 :=
  point_componentIdempotent (Bialgebra.counitAlgHom k A)

/-- The identity idempotent is idempotent in the original algebra. -/
theorem finiteIdentityIdempotent_isIdempotent : IsIdempotentElem (finiteIdentityIdempotent k A) :=
  componentIdempotent_isIdempotent A _

/-- Counit one detects the unit idempotent in the local factor. -/
theorem finiteIdentity_idempotent_eq_one {d : FiniteIdentityComponent k A}
    (hd : IsIdempotentElem d) (hε : finiteIdentityCounit k A d = 1) : d = 1 := by
  rcases component_idempotent_trivial A _ d hd with h | h
  · rw [h, map_zero] at hε
    exact (zero_ne_one hε).elim
  · exact h

/-- Inversion sends the identity idempotent to one after projection. -/
theorem finiteIdentityProjection_antipode_idempotent :
    finiteIdentityProjection k A (antipode k (finiteIdentityIdempotent k A)) = 1 := by
  apply finiteIdentity_idempotent_eq_one
  · exact ((finiteIdentityIdempotent_isIdempotent k A).map
      (antipodeAlgHom k A).toRingHom).map (finiteIdentityProjection k A).toRingHom
  · rw [finiteIdentityCounit_projection, counit_antipode, counit_finiteIdentityIdempotent]

/-- The original counit kills the ideal of the identity factor. -/
theorem finiteIdentityIdeal_counit {x : A} (hx : x ∈ finiteIdentityIdeal k A) :
    Coalgebra.counit (R := k) x = 0 := by
  rw [← finiteIdentityCounit_projection k A]
  have hq : finiteIdentityProjection k A x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  rw [hq, map_zero]

/-- The defining ideal is stable under the original antipode. -/
theorem finiteIdentityIdeal_antipode {x : A} (hx : x ∈ finiteIdentityIdeal k A) :
    antipode k x ∈ finiteIdentityIdeal k A := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change finiteIdentityProjection k A ((antipodeAlgHom k A)
    ((1 - finiteIdentityIdempotent k A) * a)) = 0
  rw [map_mul, map_sub, map_one, map_mul, map_sub, map_one]
  change (1 - finiteIdentityProjection k A (antipode k (finiteIdentityIdempotent k A))) * _ = 0
  rw [finiteIdentityProjection_antipode_idempotent, sub_self, zero_mul]

end HopfAlgebra
