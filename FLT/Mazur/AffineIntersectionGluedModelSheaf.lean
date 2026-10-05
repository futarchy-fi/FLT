/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntersectionModelSheaf
public import FLT.Mazur.ModuleUnitCocyclePullback

/-!
# The line sheaf on the explicit glued model

Transfer the colimit cocycle to the explicit glue data used in scheme-model
recovery. The transferred sheaf is locally free of rank one and is identified
with the actual pullback of the colimit sheaf along the comparison isomorphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.FCurve.ModuleSheafUnitCocycle

namespace FLT.Mazur.Approximation

universe u

variable {S : Type u} [CommRing S] {ι : Type u} [Finite ι]
  (C : NonemptyChartSet ι ⥤ CommAlgCat S)
  [∀ a b (f : a ⟶ b), IsOpenImmersion (Spec.map (CommRingCat.ofHom (C.map f).hom.toRingHom))]
  (hp : ∀ (r s t : NonemptyChartSet ι) (hrs : r ≤ s) (hrt : r ≤ t),
    IsPullback
      (Spec.map (CommRingCat.ofHom (C.map (homOfLE (le_unionChartSet_left s t))).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (C.map (homOfLE (le_unionChartSet_right s t))).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (C.map (homOfLE hrs)).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (C.map (homOfLE hrt)).hom.toRingHom)))

/-- The explicit scheme gluing is the categorical colimit of its chart diagram. -/
def affineIntersectionGluedColimitIso :
    letI := intersectionDiagram_isLocallyDirected (affineIntersectionSchemeDiagram C) hp
    (affineIntersectionGlueData C hp).glued ≅ colimit (affineIntersectionSchemeDiagram C) := by
  let := intersectionDiagram_isLocallyDirected (affineIntersectionSchemeDiagram C) hp
  exact IsColimit.coconePointUniqueUpToIso
    (Scheme.IsLocallyDirected.isColimit (affineIntersectionSchemeDiagram C))
    (colimit.isColimit (affineIntersectionSchemeDiagram C))

/-- The comparison identifies each explicit chart map with the colimit inclusion. -/
@[reassoc (attr := simp)]
theorem affineIntersectionGluedColimitIso_chart (s : NonemptyChartSet ι) :
    letI := intersectionDiagram_isLocallyDirected (affineIntersectionSchemeDiagram C) hp
    (Scheme.IsLocallyDirected.cocone (affineIntersectionSchemeDiagram C)).ι.app (.op s) ≫
      (affineIntersectionGluedColimitIso C hp).hom =
        colimit.ι (affineIntersectionSchemeDiagram C) (.op s) := by
  let := intersectionDiagram_isLocallyDirected (affineIntersectionSchemeDiagram C) hp
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (Scheme.IsLocallyDirected.isColimit (affineIntersectionSchemeDiagram C))
    (colimit.isColimit (affineIntersectionSchemeDiagram C)) (.op s)

variable (y : ∀ s, IntersectionPair s → (C.obj s)ˣ)
  (hnat : ∀ {s t} (f : s ⟶ t) (k : IntersectionPair s),
    (C.map f).hom (y s k) = (y t (intersectionPairMap f k) : C.obj t))
  (hmul : ∀ s (k : IntersectionTriple s),
    y s (k.1, k.2.1) * y s (k.2.1, k.2.2) = y s (k.1, k.2.2))

/-- The cocycle transported to the actual glue-data scheme used by recovery. -/
def affineIntersectionGluedModelCocycle :
    letI := intersectionDiagram_isLocallyDirected (affineIntersectionSchemeDiagram C) hp
    Cocycle (fun i ↦ (affineIntersectionGluedColimitIso C hp).hom ⁻¹ᵁ
      intersectionColimitOpen (affineIntersectionSchemeDiagram C) (singletonChartSet i)) := by
  let := intersectionDiagram_isLocallyDirected (affineIntersectionSchemeDiagram C) hp
  exact (affineIntersectionModelCocycle C y hnat hmul).inverseImage
    (affineIntersectionGluedColimitIso C hp).hom

/-- The genuine line sheaf on the explicit scheme model. -/
def affineIntersectionGluedModelSheaf : (affineIntersectionGlueData C hp).glued.Modules :=
  (affineIntersectionGluedModelCocycle C hp y hnat hmul).sheaf

/-- The explicit-model sheaf is the actual pullback of the colimit construction. -/
def affineIntersectionGluedModelSheafIso :
    letI := intersectionDiagram_isLocallyDirected (affineIntersectionSchemeDiagram C) hp
    (Scheme.Modules.pullback (affineIntersectionGluedColimitIso C hp).hom).obj
        (affineIntersectionModelSheaf C y hnat hmul) ≅
      affineIntersectionGluedModelSheaf C hp y hnat hmul := by
  let := intersectionDiagram_isLocallyDirected (affineIntersectionSchemeDiagram C) hp
  exact (affineIntersectionModelCocycle C y hnat hmul).pullbackIso
    (affineIntersectionGluedColimitIso C hp).hom
    (intersectionColimitOpen_singleton_cover (affineIntersectionSchemeDiagram C))

/-- The explicit-model sheaf has local rank one, by its covering trivializations. -/
theorem affineIntersectionGluedModelSheaf_rankOne :
    LocallyFreeRankOne (affineIntersectionGluedModelSheaf C hp y hnat hmul) := by
  let := intersectionDiagram_isLocallyDirected (affineIntersectionSchemeDiagram C) hp
  exact (affineIntersectionGluedModelCocycle C hp y hnat hmul).locallyFreeRankOne
    (Cocycle.inverseImage_cover
      (affineIntersectionGluedColimitIso C hp).hom
      (intersectionColimitOpen_singleton_cover (affineIntersectionSchemeDiagram C)))

end FLT.Mazur.Approximation
