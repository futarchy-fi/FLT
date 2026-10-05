/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntersectionDiagramGluing
public import FLT.Mazur.AffineSquareScalarExtension

/-!
# Scalar extension of affine intersection diagrams

Tensoring the coordinate algebras gives a genuine diagram, and compatible
algebra identifications recover its entire spectrum diagram naturally.
This is the diagram comparison needed before comparing the two gluings.
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

/-- Scalar extension of every object and arrow of an affine intersection diagram. -/
def affineIntersectionScalarExtension : NonemptyChartSet ι ⥤ CommAlgCat A :=
  algebraDiagramOfHoms (fun a ↦ A ⊗[S] D.obj a)
    (fun f ↦ affineScalarExtensionHom (S := A) (D.map f).hom)
    (fun a ↦ by
      apply Algebra.TensorProduct.ext_ring
      ext x
      simp [affineScalarExtensionHom])
    (fun f g ↦ by simp [affineScalarExtensionHom_comp])

/-- Open restriction maps remain open immersions after scalar extension. -/
instance affineIntersectionScalarExtension_map_isOpenImmersion
    [∀ a b (f : a ⟶ b),
      IsOpenImmersion (Spec.map (CommRingCat.ofHom (D.map f).hom.toRingHom))]
    (a b : NonemptyChartSet ι) (f : a ⟶ b) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (((affineIntersectionScalarExtension (A := A) D).map f).hom.toRingHom))) :=
  IsOpenImmersion.of_isPullback
    (affineScalarExtensionHom_isPullback (S := A) (D.map f).hom) inferInstance

/-- Scalar extension retains every marked cartesian union square. -/
theorem affineIntersectionScalarExtension_isPullback
    (hp : ∀ (r s t : NonemptyChartSet ι) (hrs : r ≤ s) (hrt : r ≤ t),
      IsPullback
        (Spec.map (CommRingCat.ofHom (D.map (homOfLE (le_unionChartSet_left s t))).hom.toRingHom))
        (Spec.map (CommRingCat.ofHom (D.map (homOfLE (le_unionChartSet_right s t))).hom.toRingHom))
        (Spec.map (CommRingCat.ofHom (D.map (homOfLE hrs)).hom.toRingHom))
        (Spec.map (CommRingCat.ofHom (D.map (homOfLE hrt)).hom.toRingHom)))
    (r s t : NonemptyChartSet ι) (hrs : r ≤ s) (hrt : r ≤ t) :
    let E := affineIntersectionScalarExtension (A := A) D
    IsPullback
      (Spec.map (CommRingCat.ofHom (E.map (homOfLE (le_unionChartSet_left s t))).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (E.map (homOfLE (le_unionChartSet_right s t))).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (E.map (homOfLE hrs)).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (E.map (homOfLE hrt)).hom.toRingHom)) :=
  affineScalarExtensionHom_preserves_pullback
    (D.map (homOfLE hrs)).hom (D.map (homOfLE hrt)).hom
    (D.map (homOfLE (le_unionChartSet_left s t))).hom
    (D.map (homOfLE (le_unionChartSet_right s t))).hom (hp r s t hrs hrt)

/-- Compatible recovery maps also identify restrictions in the inverse direction. -/
theorem affineIntersectionScalarExtension_inverse_naturality
    (C : NonemptyChartSet ι ⥤ CommAlgCat A)
    (e : ∀ a, A ⊗[S] D.obj a ≃ₐ[A] C.obj a)
    (he : ∀ {a b} (f : a ⟶ b), (e b).toAlgHom.comp
      (affineScalarExtensionHom (S := A) (D.map f).hom) =
      (C.map f).hom.comp (e a).toAlgHom)
    {a b : NonemptyChartSet ι} (f : a ⟶ b) :
    (affineScalarExtensionHom (S := A) (D.map f).hom).comp (e a).symm.toAlgHom =
      (e b).symm.toAlgHom.comp (C.map f).hom := by
  ext x
  apply (e b).injective
  have h := DFunLike.congr_fun (he f) ((e a).symm x)
  simpa using h

/-- Full algebra recovery gives a natural isomorphism of the spectrum diagrams. -/
def affineIntersectionScalarExtensionSpecIso
    (C : NonemptyChartSet ι ⥤ CommAlgCat A)
    (e : ∀ a, A ⊗[S] D.obj a ≃ₐ[A] C.obj a)
    (he : ∀ {a b} (f : a ⟶ b), (e b).toAlgHom.comp
      (affineScalarExtensionHom (S := A) (D.map f).hom) =
      (C.map f).hom.comp (e a).toAlgHom) :
    affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D) ≅
      affineIntersectionSchemeDiagram C := by
  refine NatIso.ofComponents
    (fun a ↦ Scheme.Spec.mapIso (e a.unop).toRingEquiv.toCommRingCatIso.symm.op) ?_
  intro a b f
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact congrArg (fun g ↦ CommRingCat.ofHom g.toRingHom)
    (affineIntersectionScalarExtension_inverse_naturality D C e he f.unop)

end FLT.Mazur.Approximation
