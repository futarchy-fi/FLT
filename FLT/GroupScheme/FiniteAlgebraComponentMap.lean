/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteAlgebraPointComponent

/-! # Restricting maps and isomorphisms to pointed local factors -/

@[expose] public noncomputable section

namespace FiniteAlgebra

variable {k A B : Type*} [Field k] [CommRing A] [CommRing B]
  [IsArtinianRing A] [IsArtinianRing B] [Algebra k A] [Algebra k B]

/-- A point-preserving algebra map restricts to the corresponding local factors. -/
def pointComponentMap (α : A →ₐ[k] k) (β : B →ₐ[k] k) (f : A →ₐ[k] B)
    (hf : β.comp f = α) : PointComponent α →ₐ[k] PointComponent β :=
  Ideal.Quotient.liftₐ _ ((pointProjection β).comp f) (by
    change Ideal.span {1 - componentIdempotent A (pointComponentIndex α)} ≤
      RingHom.ker ((pointProjection β).comp f)
    apply Ideal.span_le.mpr
    rintro x (rfl : x = _)
    have hd := ((componentIdempotent_isIdempotent A (pointComponentIndex α)).map f.toRingHom).map
      (pointProjection β).toRingHom
    have he : pointProjection β (f (componentIdempotent A (pointComponentIndex α))) = 1 := by
      rcases component_idempotent_trivial B _ _ hd with h | h
      · have hh := congrArg (componentPoint β) h
        rw [map_zero] at hh
        change β (f (componentIdempotent A (pointComponentIndex α))) = 0 at hh
        have hp := AlgHom.congr_fun hf (componentIdempotent A (pointComponentIndex α))
        change β (f (componentIdempotent A (pointComponentIndex α))) = _ at hp
        rw [hp, point_componentIdempotent] at hh
        exact (one_ne_zero hh).elim
      · exact h
    change pointProjection β (f (1 - componentIdempotent A (pointComponentIndex α))) = 0
    rw [map_sub, map_one, map_sub, map_one, he, sub_self])

/-- The restricted map is the original map on polynomial representatives. -/
theorem pointComponentMap_projection (α : A →ₐ[k] k) (β : B →ₐ[k] k) (f : A →ₐ[k] B)
    (hf : β.comp f = α) (a : A) :
    pointComponentMap α β f hf (pointProjection α a) = pointProjection β (f a) := rfl

/-- A point-preserving algebra equivalence restricts to an equivalence of local factors. -/
def pointComponentEquiv (α : A →ₐ[k] k) (β : B →ₐ[k] k) (e : A ≃ₐ[k] B)
    (he : β.comp e.toAlgHom = α) : PointComponent α ≃ₐ[k] PointComponent β := by
  have hei : α.comp e.symm.toAlgHom = β := by
    ext b
    have h := AlgHom.congr_fun he (e.symm b)
    simpa using h.symm
  apply AlgEquiv.ofAlgHom (pointComponentMap α β e.toAlgHom he)
    (pointComponentMap β α e.symm.toAlgHom hei)
  · apply AlgHom.ext
    intro b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    change pointProjection β (e (e.symm b)) = pointProjection β b
    rw [e.apply_symm_apply]
  · apply AlgHom.ext
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change pointProjection α (e.symm (e a)) = pointProjection α a
    rw [e.symm_apply_apply]

/-- The component equivalence retains the coordinate formula of the original equivalence. -/
theorem pointComponentEquiv_projection (α : A →ₐ[k] k) (β : B →ₐ[k] k) (e : A ≃ₐ[k] B)
    (he : β.comp e.toAlgHom = α) (a : A) :
    pointComponentEquiv α β e he (pointProjection α a) = pointProjection β (e a) := rfl

end FiniteAlgebra
