/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicFormalPresentationHom
public import FLT.Mazur.AdicExtensionProjectionKernel

/-!
# The actual conormal module of a completed square-zero extension

A square-zero ideal is its own conormal module. Applying this to a
completed infinitesimal extension identifies its conormal module with
the actual kernel of its completed projection.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicSquareZeroConormal

set_option backward.isDefEq.respectTransparency false

variable {S : Type*} [CommRing S] (L : Ideal S)

/-- A square-zero ideal maps isomorphically to its conormal module. -/
def idealEquiv (h : L ^ 2 = ⊥) : L ≃ₗ[S] L.Cotangent :=
  LinearEquiv.ofBijective L.toCotangent ⟨by
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    have hz := (L.toCotangent_eq_zero x).mp hx
    rw [h, Submodule.mem_bot] at hz
    exact Subtype.ext hz, L.toCotangent_surjective⟩

/-- This identification is the original quotient-to-conormal map. -/
@[simp] theorem idealEquiv_apply (h : L ^ 2 = ⊥) (x : L) :
    idealEquiv L h x = L.toCotangent x := rfl

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (P : Algebra.Extension.{u} R A) (I : Ideal A) [IsNoetherianRing P.Ring]

/-- The conormal of a completed square-zero presentation is its actual projection kernel. -/
def completedEquiv (h : P.ker ^ 2 = ⊥) :
    (AdicFormalPresentationHom.completed P I).Cotangent ≃ₗ[
      (AdicFormalPresentationHom.completed P I).Ring]
      (AdicFormalPresentationHom.completed P I).ker := by
  let C := AdicFormalPresentationHom.completed P I
  let e : C.Cotangent ≃ₗ[C.Ring] C.ker.Cotangent :=
    { __ := AddEquiv.refl _
      map_smul' := Algebra.Extension.Cotangent.val_smul' }
  exact e ≪≫ₗ (idealEquiv C.ker
    (AdicExtensionProjection.ker_projection_square_zero P I h)).symm

/-- On an original kernel class, the conormal identification recovers that exact class. -/
theorem completedEquiv_mk (h : P.ker ^ 2 = ⊥)
    (x : (AdicFormalPresentationHom.completed P I).ker) :
    completedEquiv P I h (Algebra.Extension.Cotangent.mk x) = x := by
  change (idealEquiv (AdicFormalPresentationHom.completed P I).ker
    (AdicExtensionProjection.ker_projection_square_zero P I h)).symm
    ((AdicFormalPresentationHom.completed P I).ker.toCotangent x) = x
  exact (idealEquiv _ _).symm_apply_apply x

end FLT.Mazur.AdicSquareZeroConormal
