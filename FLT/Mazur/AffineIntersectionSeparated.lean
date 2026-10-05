/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntersectionGluingBaseChange
public import FLT.Mazur.IntersectionGluingCharts
public import FLT.Mazur.SeparatedOverlapPullback
public import FLT.Mazur.AffineProductMap

/-!
# Separatedness of an affine intersection gluing

Closed product maps for union-label overlaps imply separatedness of the
constructed structural morphism. The proof uses the actual chart pullbacks
in the colimit, then transfers along the canonical gluing comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {S : Type u} [CommRing S] {ι : Type v} [Finite ι]
  (C : NonemptyChartSet ι ⥤ CommAlgCat S)
  [∀ a b (f : a ⟶ b), IsOpenImmersion (Spec.map (CommRingCat.ofHom (C.map f).hom.toRingHom))]
  (hc : ∀ a b, IsClosedImmersion (Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.productMap
      (C.map (homOfLE (le_unionChartSet_left a b))).hom
      (C.map (homOfLE (le_unionChartSet_right a b))).hom).toRingHom)))

include hc

/-- Closed affine overlaps make the colimit structural morphism separated. -/
theorem affineIntersectionColimitToBase_isSeparated
    [((affineIntersectionSchemeDiagram C) ⋙ Scheme.forget).IsLocallyDirected] :
    IsSeparated (colimit.desc _ (affineIntersectionBaseCocone C)) := by
  let F := affineIntersectionSchemeDiagram C
  let q := colimit.desc F (affineIntersectionBaseCocone C)
  have hclosed (i j : (NonemptyChartSet ι)ᵒᵖ) :
      IsClosedImmersion (pullback.lift (f := colimit.ι F i ≫ q) (g := colimit.ι F j ≫ q)
        (F.map (homOfLE (le_unionChartSet_left i.unop j.unop)).op)
        (F.map (homOfLE (le_unionChartSet_right i.unop j.unop)).op)
        (by simp only [← Category.assoc, colimit.w])) := by
    have hi : colimit.ι F i ≫ q =
        Spec.map (CommRingCat.ofHom (algebraMap S (C.obj i.unop))) := colimit.ι_desc _ _
    have hj : colimit.ι F j ≫ q =
        Spec.map (CommRingCat.ofHom (algebraMap S (C.obj j.unop))) := colimit.ι_desc _ _
    let f := (C.map (homOfLE (le_unionChartSet_left i.unop j.unop))).hom
    let g := (C.map (homOfLE (le_unionChartSet_right i.unop j.unop))).hom
    have he : pullback.lift (f := colimit.ι F i ≫ q) (g := colimit.ι F j ≫ q)
        (F.map (homOfLE (le_unionChartSet_left i.unop j.unop)).op)
        (F.map (homOfLE (le_unionChartSet_right i.unop j.unop)).op)
        (by simp only [← Category.assoc, colimit.w]) =
      pullback.lift (Spec.map (CommRingCat.ofHom f.toRingHom))
        (Spec.map (CommRingCat.ofHom g.toRingHom)) (affineProductMap_condition f g) ≫
          (pullback.congrHom hi.symm hj.symm).hom := by
      apply pullback.hom_ext <;> simp [F, affineIntersectionSchemeDiagram, f, g]
    rw [he]
    let := (affineProductMap_isClosedImmersion_iff f g).mp (hc i.unop j.unop)
    infer_instance
  exact FLT.Mazur.SeparatedOpenCover.of_overlap_pullbacks q
    (Scheme.IsLocallyDirected.openCover F)
    (fun i j ↦ F.obj (.op (unionChartSet i.unop j.unop)))
    (fun i j ↦ F.map (homOfLE (le_unionChartSet_left i.unop j.unop)).op)
    (fun i j ↦ F.map (homOfLE (le_unionChartSet_right i.unop j.unop)).op)
    (fun i j ↦ intersection_colimit_isPullback F i.unop j.unop) hclosed

/-- The explicit gluing has separated structural morphism over its coefficient ring. -/
theorem affineIntersectionGluedToBase_isSeparated
    (hp : ∀ (r s t : NonemptyChartSet ι) (hrs : r ≤ s) (hrt : r ≤ t),
      IsPullback
        (Spec.map (CommRingCat.ofHom (C.map (homOfLE (le_unionChartSet_left s t))).hom.toRingHom))
        (Spec.map (CommRingCat.ofHom (C.map (homOfLE (le_unionChartSet_right s t))).hom.toRingHom))
        (Spec.map (CommRingCat.ofHom (C.map (homOfLE hrs)).hom.toRingHom))
        (Spec.map (CommRingCat.ofHom (C.map (homOfLE hrt)).hom.toRingHom))) :
    IsSeparated (affineIntersectionGluedToBase C hp) := by
  let F := affineIntersectionSchemeDiagram C
  let := intersectionDiagram_isLocallyDirected F hp
  let e := (Scheme.IsLocallyDirected.isColimit F).coconePointUniqueUpToIso
    (colimit.isColimit F)
  have he : affineIntersectionGluedToBase C hp =
      e.hom ≫ colimit.desc F (affineIntersectionBaseCocone C) := by
    apply (Scheme.IsLocallyDirected.isColimit F).hom_ext
    intro a
    simp [affineIntersectionGluedToBase, e]
  rw [he]
  let := affineIntersectionColimitToBase_isSeparated C hc
  infer_instance

end FLT.Mazur.Approximation
