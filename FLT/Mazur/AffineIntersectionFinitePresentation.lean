/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntersectionGluingBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Finiteness of affine intersection gluings

A finite diagram of affine charts has quasi-compact gluing. If its chart
algebras are finitely presented, the glued structural map is locally of
finite presentation. These properties concern the constructed model itself.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {S : Type u} [CommRing S] {ι : Type v} [Finite ι]
  (D : NonemptyChartSet ι ⥤ CommAlgCat S)
  [∀ a b (f : a ⟶ b), IsOpenImmersion (Spec.map (CommRingCat.ofHom (D.map f).hom.toRingHom))]

/-- A finite affine intersection colimit is compact. -/
theorem affineIntersectionColimit_compactSpace
    [((affineIntersectionSchemeDiagram D) ⋙ Scheme.forget).IsLocallyDirected] :
    CompactSpace ↑(colimit (affineIntersectionSchemeDiagram D)) := by
  let F := affineIntersectionSchemeDiagram D
  let U := Scheme.IsLocallyDirected.openCover F
  have : Finite U.I₀ := inferInstanceAs (Finite (NonemptyChartSet ι)ᵒᵖ)
  have : ∀ i, CompactSpace (U.X i) := fun i ↦
    inferInstanceAs (CompactSpace (Spec (.of (D.obj i.unop))))
  exact U.compactSpace

/-- Finite presentation of each chart gives local finite presentation of the colimit map. -/
theorem affineIntersectionColimitToBase_locallyOfFinitePresentation
    [((affineIntersectionSchemeDiagram D) ⋙ Scheme.forget).IsLocallyDirected]
    [∀ a, Algebra.FinitePresentation S (D.obj a)] :
    LocallyOfFinitePresentation (colimit.desc _ (affineIntersectionBaseCocone D)) := by
  apply IsZariskiLocalAtSource.of_openCover (Scheme.IsLocallyDirected.openCover _)
  intro i
  change LocallyOfFinitePresentation
    (colimit.ι (affineIntersectionSchemeDiagram D) i ≫ _)
  rw [colimit.ι_desc]
  change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap S _)))
  rw [LocallyOfFinitePresentation.SpecMap_iff, CommRingCat.hom_ofHom,
    RingHom.finitePresentation_algebraMap]
  infer_instance

variable (hp : ∀ (r s t : NonemptyChartSet ι) (hrs : r ≤ s) (hrt : r ≤ t),
    IsPullback
      (Spec.map (CommRingCat.ofHom (D.map (homOfLE (le_unionChartSet_left s t))).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (D.map (homOfLE (le_unionChartSet_right s t))).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (D.map (homOfLE hrs)).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (D.map (homOfLE hrt)).hom.toRingHom)))

/-- The explicit finite affine gluing is compact. -/
theorem affineIntersectionGlued_compactSpace :
    CompactSpace (affineIntersectionGlueData D hp).glued := by
  let F := affineIntersectionSchemeDiagram D
  let := intersectionDiagram_isLocallyDirected F hp
  let e := (Scheme.IsLocallyDirected.isColimit F).coconePointUniqueUpToIso
    (colimit.isColimit F)
  exact @Homeomorph.compactSpace _ _ _ _ (affineIntersectionColimit_compactSpace D)
    (Scheme.homeoOfIso e).symm

/-- The explicit finite affine gluing is quasi-compact over its coefficient base. -/
theorem affineIntersectionGluedToBase_quasiCompact :
    QuasiCompact (affineIntersectionGluedToBase D hp) := by
  let := affineIntersectionGlued_compactSpace D hp
  exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance

/-- Finitely presented chart algebras give a locally finitely presented glued model. -/
theorem affineIntersectionGluedToBase_locallyOfFinitePresentation
    [∀ a, Algebra.FinitePresentation S (D.obj a)] :
    LocallyOfFinitePresentation (affineIntersectionGluedToBase D hp) := by
  let F := affineIntersectionSchemeDiagram D
  let := intersectionDiagram_isLocallyDirected F hp
  let e := (Scheme.IsLocallyDirected.isColimit F).coconePointUniqueUpToIso
    (colimit.isColimit F)
  have he : affineIntersectionGluedToBase D hp =
      e.hom ≫ colimit.desc F (affineIntersectionBaseCocone D) := by
    apply (Scheme.IsLocallyDirected.isColimit F).hom_ext
    intro a
    simp [affineIntersectionGluedToBase, e]
  rw [he]
  let := affineIntersectionColimitToBase_locallyOfFinitePresentation D
  infer_instance

end FLT.Mazur.Approximation
