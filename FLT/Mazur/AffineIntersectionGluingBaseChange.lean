/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntersectionProjection
public import FLT.Mazur.EquifiberedGluingBaseChange

/-!
# Coefficient base change of glued affine intersection diagrams

Gluing the tensor-extended coordinate diagram is the pullback of the
original glued scheme along the coefficient map. Both structural maps
are the maps constructed by gluing the algebra structure maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {S A : Type u} [CommRing S] [CommRing A] [Algebra S A]
  {ι : Type v} [Finite ι] (D : NonemptyChartSet ι ⥤ CommAlgCat S)
  [∀ a b (f : a ⟶ b),
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (D.map f).hom.toRingHom))]

/-- Open algebra restriction maps induce open arrows in the spectrum diagram. -/
instance affineIntersectionSchemeDiagram_map_isOpenImmersion
    {a b : (NonemptyChartSet ι)ᵒᵖ} (f : a ⟶ b) :
    IsOpenImmersion ((affineIntersectionSchemeDiagram D).map f) :=
  inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (D.map f.unop).hom.toRingHom)))

variable (hp : ∀ (r s t : NonemptyChartSet ι) (hrs : r ≤ s) (hrt : r ≤ t),
    IsPullback
      (Spec.map (CommRingCat.ofHom (D.map (homOfLE (le_unionChartSet_left s t))).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (D.map (homOfLE (le_unionChartSet_right s t))).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (D.map (homOfLE hrs)).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (D.map (homOfLE hrt)).hom.toRingHom)))

/-- Projection of the glued scalar extension to the glued original diagram. -/
def affineIntersectionGluingProjection :
    (affineIntersectionGlueData (affineIntersectionScalarExtension (A := A) D)
      (affineIntersectionScalarExtension_isPullback D hp)).glued ⟶
      (affineIntersectionGlueData D hp).glued := by
  letI := intersectionDiagram_isLocallyDirected (affineIntersectionSchemeDiagram D) hp
  letI := intersectionDiagram_isLocallyDirected
    (affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D))
    (affineIntersectionScalarExtension_isPullback D hp)
  exact (Scheme.IsLocallyDirected.isColimit _).map
    (Scheme.IsLocallyDirected.cocone _) (affineIntersectionProjection (A := A) D)

/-- Gluing commutes with coefficient base change, with the actual structural maps. -/
theorem affineIntersectionGluing_isPullback :
    IsPullback (affineIntersectionGluingProjection (A := A) D hp)
      (affineIntersectionGluedToBase (affineIntersectionScalarExtension (A := A) D)
        (affineIntersectionScalarExtension_isPullback D hp))
      (affineIntersectionGluedToBase D hp)
      (Spec.map (CommRingCat.ofHom (algebraMap S A))) := by
  let := intersectionDiagram_isLocallyDirected (affineIntersectionSchemeDiagram D) hp
  let := intersectionDiagram_isLocallyDirected
    (affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D))
    (affineIntersectionScalarExtension_isPullback D hp)
  exact equifibered_cocone_baseChange (affineIntersectionProjection (A := A) D)
    (affineIntersectionProjection_equifibered D)
    (Scheme.IsLocallyDirected.isColimit _) (Scheme.IsLocallyDirected.isColimit _)
    (affineIntersectionGluingProjection D hp)
    (affineIntersectionBaseCocone (affineIntersectionScalarExtension D))
    (affineIntersectionBaseCocone D) _
    (fun i ↦ IsColimit.ι_map _ _ _ i) (affineIntersectionProjection_isPullback D)

/-- The scalar-extended gluing identifies with the pullback of the integer model gluing. -/
def affineIntersectionGluingPullbackIso :
    (affineIntersectionGlueData (affineIntersectionScalarExtension (A := A) D)
      (affineIntersectionScalarExtension_isPullback D hp)).glued ≅
      pullback (affineIntersectionGluedToBase D hp)
        (Spec.map (CommRingCat.ofHom (algebraMap S A))) :=
  (affineIntersectionGluing_isPullback D hp).isoPullback

/-- The base-change identification is over the new coefficient spectrum. -/
@[reassoc (attr := simp)]
theorem affineIntersectionGluingPullbackIso_snd :
    (affineIntersectionGluingPullbackIso (A := A) D hp).hom ≫ pullback.snd _ _ =
      affineIntersectionGluedToBase (affineIntersectionScalarExtension (A := A) D)
        (affineIntersectionScalarExtension_isPullback D hp) :=
  IsPullback.isoPullback_hom_snd _

/-- The base-change identification retains the projection to the original gluing. -/
@[reassoc (attr := simp)]
theorem affineIntersectionGluingPullbackIso_fst :
    (affineIntersectionGluingPullbackIso (A := A) D hp).hom ≫ pullback.fst _ _ =
      affineIntersectionGluingProjection D hp :=
  IsPullback.isoPullback_hom_fst _

end FLT.Mazur.Approximation
