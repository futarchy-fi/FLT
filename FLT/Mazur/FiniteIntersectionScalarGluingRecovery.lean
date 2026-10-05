/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntersectionScalarExtension
public import FLT.Mazur.FiniteIntersectionCoordinateGluing

/-!
# Recovery after extending the model coordinates

A compatible recovery of all tensor-extended model algebras induces an
isomorphism from their constructed gluing to the original covered scheme.
This recovers gluing after extending the coordinates. It does not yet
identify that scheme with the pullback of the glued integer model.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

/-- Gluing the scalar-extended coordinate models recovers the original covered scheme. -/
def finiteIntersectionScalarGluingIso {S A : Type u} [CommRing S] [CommRing A] [Algebra S A]
    {X : Scheme.{u}} {ι : Type v} [Finite ι] (U : ι → X.Opens)
    (p : X ⟶ Spec (.of A)) [X.IsSeparated] (hU : ∀ i, IsAffineOpen (U i))
    (hcover : iSup U = ⊤) (D : NonemptyChartSet ι ⥤ CommAlgCat S)
    [∀ a b (f : a ⟶ b),
      IsOpenImmersion (Spec.map (CommRingCat.ofHom (D.map f).hom.toRingHom))]
    (hp : ∀ (r s t : NonemptyChartSet ι) (hrs : r ≤ s) (hrt : r ≤ t),
      IsPullback
        (Spec.map (CommRingCat.ofHom (D.map (homOfLE (le_unionChartSet_left s t))).hom.toRingHom))
        (Spec.map (CommRingCat.ofHom (D.map (homOfLE (le_unionChartSet_right s t))).hom.toRingHom))
        (Spec.map (CommRingCat.ofHom (D.map (homOfLE hrs)).hom.toRingHom))
        (Spec.map (CommRingCat.ofHom (D.map (homOfLE hrt)).hom.toRingHom)))
    (e : ∀ a, A ⊗[S] D.obj a ≃ₐ[A] (finiteIntersectionSectionDiagram U p).obj a)
    (he : ∀ {a b} (f : a ⟶ b), (e b).toAlgHom.comp
      (affineScalarExtensionHom (S := A) (D.map f).hom) =
      ((finiteIntersectionSectionDiagram U p).map f).hom.comp (e a).toAlgHom) :
    (affineIntersectionGlueData (affineIntersectionScalarExtension (A := A) D)
      (affineIntersectionScalarExtension_isPullback D hp)).glued ≅ X := by
  let F := affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D)
  letI : ∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f) :=
    fun {_ _} f ↦ affineIntersectionScalarExtension_map_isOpenImmersion D _ _ f.unop
  exact intersectionDiagramGluingIsoOfNatIso F
    (affineIntersectionScalarExtension_isPullback D hp)
    (finiteIntersectionSchemeDiagram U) (finiteIntersectionOpen_isPullback U)
    (affineIntersectionScalarExtensionSpecIso D (finiteIntersectionSectionDiagram U p) e he ≪≫
      (finiteIntersectionCoordinateDiagramIso U p hU).symm) ≪≫
    finiteIntersectionGluingIso U hcover

end FLT.Mazur.Approximation
