/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalQuotientAlgebra

/-!
# Projection to the literal iterated principal quotient

The second denominator is the actual image of a first-level fraction. The
kernel of the projection is exactly the twice extended ambient relation ideal.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.IteratedQuotientProjection

universe u v

variable {P : Type u} [CommRing P] (I : Ideal P) (r : P) (s : Localization.Away r)

/-- The second localization uses the projected first-level denominator literally. -/
abbrev Target := Localization.Away (PrincipalQuotientProjection.projection I r s)

/-- Projection to the iterated localization of the ambient quotient. -/
def projection : Localization.Away s →+* Target I r s :=
  NoetherianRelationContraction.principalCoefficientMap
    (PrincipalQuotientProjection.projection I r) s

/-- Projection commutes with localization of every first-level fraction. -/
@[simp] theorem projection_algebraMap (x : Localization.Away r) :
    projection I r s (algebraMap _ (Localization.Away s) x) =
      algebraMap (PrincipalQuotientProjection.Target I r) (Target I r s)
        (PrincipalQuotientProjection.projection I r x) :=
  RingHom.congr_fun (NoetherianRelationContraction.principalCoefficientMap_comp
    (PrincipalQuotientProjection.projection I r) s) x

/-- Every element of the literal iterated quotient has an unquotiented representative. -/
theorem projection_surjective : Function.Surjective (projection I r s) :=
  IsLocalization.map_surjective_of_surjective (Submonoid.powers s)
    (Localization.Away s) (Target I r s)
    (PrincipalQuotientProjection.projection_surjective I r)

/-- The kernel is the double localization of the same ambient ideal. -/
theorem ker_projection :
    RingHom.ker (projection I r s) =
      (I.map (algebraMap P (Localization.Away r))).map
        (algebraMap (Localization.Away r) (Localization.Away s)) := by
  have h := IsLocalization.ker_map (S := Localization.Away s) (Target I r s)
    (PrincipalQuotientProjection.projection I r)
    (Submonoid.map_powers (PrincipalQuotientProjection.projection I r) s)
  change RingHom.ker (projection I r s) =
    (RingHom.ker (PrincipalQuotientProjection.projection I r)).map
      (algebraMap (Localization.Away r) (Localization.Away s)) at h
  simpa only [PrincipalQuotientProjection.ker_projection] using h

/-- Maps out of an iterated quotient are determined on the original ambient ring. -/
theorem hom_ext {T : Type*} [CommRing T] {f g : Target I r s →+* T}
    (h : ∀ x : P,
      f (algebraMap (PrincipalQuotientProjection.Target I r) (Target I r s)
        (algebraMap (P ⧸ I) (PrincipalQuotientProjection.Target I r)
          (Ideal.Quotient.mk I x))) =
      g (algebraMap (PrincipalQuotientProjection.Target I r) (Target I r s)
        (algebraMap (P ⧸ I) (PrincipalQuotientProjection.Target I r)
          (Ideal.Quotient.mk I x)))) : f = g := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (PrincipalQuotientProjection.projection I r s))
  exact PrincipalQuotientProjection.hom_ext I r h

variable (R : Type v) [CommRing R] [Algebra R P]

/-- The iterated projection respects the unchanged original base algebra structure. -/
def projectionAlgHom : Localization.Away s →ₐ[R] Target I r s where
  __ := projection I r s
  commutes' x := by
    change projection I r s (algebraMap R (Localization.Away s) x) =
      algebraMap R (Target I r s) x
    rw [IsScalarTower.algebraMap_apply R (Localization.Away r), projection_algebraMap]
    have h : PrincipalQuotientProjection.projection I r
        (algebraMap R (Localization.Away r) x) =
        algebraMap R (PrincipalQuotientProjection.Target I r) x :=
      (PrincipalQuotientProjection.projectionAlgHom R I r).commutes x
    rw [h]
    exact (IsScalarTower.algebraMap_apply R
      (PrincipalQuotientProjection.Target I r) (Target I r s) x).symm

/-- The algebra projection has the constructed ring map as its underlying map. -/
theorem projectionAlgHom_toRingHom :
    (projectionAlgHom I r s R).toRingHom = projection I r s := rfl

end FLT.Mazur.IteratedQuotientProjection
