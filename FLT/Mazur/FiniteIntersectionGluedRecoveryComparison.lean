/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntersectionGluedModelSheaf
public import FLT.Mazur.FiniteIntersectionScalarColimitRecovery

/-!
# Comparing explicit gluing and colimit recovery

The explicit gluing projection and recovery agree with their colimit versions.
These equalities allow line-sheaf recovery to use the same scheme morphism as
the cartesian coefficient recovery square.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

variable {S A : Type u} [CommRing S] [CommRing A] [Algebra S A]
  {X : Scheme.{u}} {ι : Type u} [Finite ι] (U : ι → X.Opens)
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
    ((finiteIntersectionSectionDiagram U p).map f).hom.comp (e a).toAlgHom)

/-- Explicit scalar recovery is colimit recovery after the gluing comparison. -/
@[reassoc]
theorem finiteIntersectionScalarGluing_colimit :
    letI := intersectionDiagram_isLocallyDirected
      (affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D))
      (affineIntersectionScalarExtension_isPullback D hp)
    (affineIntersectionGluedColimitIso (affineIntersectionScalarExtension (A := A) D)
      (affineIntersectionScalarExtension_isPullback D hp)).hom ≫
        (finiteIntersectionScalarColimitIso U p hU hcover D e he).hom =
      (finiteIntersectionScalarGluingIso U p hU hcover D hp e he).hom := by
  let F := affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D)
  let := intersectionDiagram_isLocallyDirected F
    (affineIntersectionScalarExtension_isPullback D hp)
  apply (Scheme.IsLocallyDirected.isColimit F).hom_ext
  intro a
  rw [← Category.assoc, affineIntersectionGluedColimitIso_chart,
    finiteIntersectionScalarColimitIso_chart]
  simp only [finiteIntersectionScalarGluingIso, intersectionDiagramGluingIsoOfNatIso,
    finiteIntersectionGluingIso, Iso.trans_hom, Category.assoc,
    IsColimit.comp_coconePointUniqueUpToIso_hom_assoc,
    colimit.cocone_ι, HasColimit.ι_isoOfNatIso_hom_assoc,
    colimit.comp_coconePointUniqueUpToIso_hom_assoc,
    IsColimit.comp_coconePointUniqueUpToIso_hom]
  rfl

/-- The explicit coefficient projection agrees with the map of colimits. -/
@[reassoc]
theorem affineIntersectionGluingProjection_colimit :
    letI := intersectionDiagram_isLocallyDirected (affineIntersectionSchemeDiagram D) hp
    letI := intersectionDiagram_isLocallyDirected
      (affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D))
      (affineIntersectionScalarExtension_isPullback D hp)
    affineIntersectionGluingProjection (A := A) D hp ≫
        (affineIntersectionGluedColimitIso D hp).hom =
      (affineIntersectionGluedColimitIso (affineIntersectionScalarExtension (A := A) D)
        (affineIntersectionScalarExtension_isPullback D hp)).hom ≫
          colimMap (affineIntersectionProjection (A := A) D) := by
  let := intersectionDiagram_isLocallyDirected (affineIntersectionSchemeDiagram D) hp
  let F := affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D)
  let := intersectionDiagram_isLocallyDirected F
    (affineIntersectionScalarExtension_isPullback D hp)
  apply (Scheme.IsLocallyDirected.isColimit F).hom_ext
  intro a
  dsimp only [F]
  simp only [affineIntersectionGluingProjection, ← Category.assoc]
  rw [IsColimit.ι_map, Category.assoc, affineIntersectionGluedColimitIso_chart,
    affineIntersectionGluedColimitIso_chart, ι_colimMap]

/-- The original-to-model morphism is the colimit recovery morphism after comparison. -/
@[reassoc]
theorem finiteIntersectionModelRecovery_colimit :
    letI := intersectionDiagram_isLocallyDirected (affineIntersectionSchemeDiagram D) hp
    letI := intersectionDiagram_isLocallyDirected
      (affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D))
      (affineIntersectionScalarExtension_isPullback D hp)
    ((finiteIntersectionScalarGluingIso U p hU hcover D hp e he).inv ≫
        affineIntersectionGluingProjection (A := A) D hp) ≫
        (affineIntersectionGluedColimitIso D hp).hom =
      (finiteIntersectionScalarColimitIso U p hU hcover D e he).inv ≫
        colimMap (affineIntersectionProjection (A := A) D) := by
  let := intersectionDiagram_isLocallyDirected (affineIntersectionSchemeDiagram D) hp
  let := intersectionDiagram_isLocallyDirected
    (affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D))
    (affineIntersectionScalarExtension_isPullback D hp)
  rw [Category.assoc, affineIntersectionGluingProjection_colimit D hp, ← Category.assoc]
  congr 1
  rw [← cancel_mono (finiteIntersectionScalarColimitIso U p hU hcover D e he).hom,
    Category.assoc, finiteIntersectionScalarGluing_colimit U p hU hcover D hp e he,
    Iso.inv_hom_id, Iso.inv_hom_id]

end FLT.Mazur.Approximation
