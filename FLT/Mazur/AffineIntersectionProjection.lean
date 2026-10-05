/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntersectionScalarExtension
public import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# Projection of the scalar-extended intersection diagram

The tensor inclusions define an equifibered natural transformation on
spectra. Its components are the affine coefficient base-change squares.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

variable {S A : Type u} [CommRing S] [CommRing A] [Algebra S A]
  {ι : Type v} (D : NonemptyChartSet ι ⥤ CommAlgCat S)

/-- Projection from the scalar-extended spectrum diagram to the original diagram. -/
def affineIntersectionProjection :
    affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D) ⟶
      affineIntersectionSchemeDiagram D where
  app a := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : D.obj a.unop →ₐ[S] A ⊗[S] D.obj a.unop).toRingHom)
  naturality {a b} f := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl

/-- Every naturality square of the tensor projection is cartesian. -/
theorem affineIntersectionProjection_equifibered :
    (affineIntersectionProjection (A := A) D).Equifibered := by
  intro a b f
  exact (affineScalarExtensionHom_isPullback (S := A) (D.map f.unop).hom).flip

/-- Each chart of the tensor projection is the coefficient base change. -/
theorem affineIntersectionProjection_isPullback (a : (NonemptyChartSet ι)ᵒᵖ) :
    IsPullback ((affineIntersectionProjection (A := A) D).app a)
      ((affineIntersectionBaseCocone (affineIntersectionScalarExtension (A := A) D)).ι.app a)
      ((affineIntersectionBaseCocone D).ι.app a)
      (Spec.map (CommRingCat.ofHom (algebraMap S A))) :=
  integerModel_isPullback (AlgEquiv.refl : A ⊗[S] D.obj a.unop ≃ₐ[A] A ⊗[S] D.obj a.unop)

end FLT.Mazur.Approximation
