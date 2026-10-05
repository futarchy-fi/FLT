/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineProductMap
public import FLT.Mazur.FiniteIntersectionCoordinateSquares

/-!
# Closed diagonal charts in actual intersection coordinates

For each pair of finite intersections of affine opens in a separated scheme,
the coordinate map from the tensor product to the union-label intersection
is a closed immersion on spectra. These are the geometric inputs to
simultaneous descent of overlap product maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {ι : Type v}
  (U : ι → X.Opens) (p : X ⟶ Spec (.of A)) [X.IsSeparated]
  (hU : ∀ i, IsAffineOpen (U i))

include hU

/-- The coordinate union square is the actual intersection over the original scheme. -/
theorem finiteIntersectionSectionDiagram_pair_isPullback (s t : NonemptyChartSet ι) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (((finiteIntersectionSectionDiagram U p).map
        (homOfLE (le_unionChartSet_left s t))).hom.toRingHom)))
      (Spec.map (CommRingCat.ofHom (((finiteIntersectionSectionDiagram U p).map
        (homOfLE (le_unionChartSet_right s t))).hom.toRingHom)))
      ((finiteIntersectionSectionSpecIso U p hU s).inv ≫ (finiteIntersectionOpen U s).ι)
      ((finiteIntersectionSectionSpecIso U p hU t).inv ≫ (finiteIntersectionOpen U t).ι) := by
  have hp : IsPullback
      (X.homOfLE (finiteIntersectionOpen_antitone U (le_unionChartSet_left s t)))
      (X.homOfLE (finiteIntersectionOpen_antitone U (le_unionChartSet_right s t)))
      (finiteIntersectionOpen U s).ι (finiteIntersectionOpen U t).ι := by
    apply (isPullback_opens_inf (finiteIntersectionOpen U s)
      (finiteIntersectionOpen U t)).of_iso
      (X.isoOfEq (finiteIntersectionOpen_union U s t).symm)
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp [← cancel_mono (finiteIntersectionOpen U s).ι]
    · simp [← cancel_mono (finiteIntersectionOpen U t).ι]
    · simp
    · simp
  apply hp.of_iso
    (finiteIntersectionSectionSpecIso U p hU (unionChartSet s t))
    (finiteIntersectionSectionSpecIso U p hU s)
    (finiteIntersectionSectionSpecIso U p hU t) (Iso.refl _)
  · exact (finiteIntersectionSectionSpecIso_naturality U p hU _).symm
  · exact (finiteIntersectionSectionSpecIso_naturality U p hU _).symm
  · simp
  · simp

/-- The spectrum chart identification retains its structural map over the base. -/
theorem finiteIntersectionSectionSpecIso_inv_over (s : NonemptyChartSet ι) :
    (finiteIntersectionSectionSpecIso U p hU s).inv ≫ (finiteIntersectionOpen U s).ι ≫ p =
      Spec.map (CommRingCat.ofHom
        (algebraMap A ((finiteIntersectionSectionDiagram U p).obj s))) := by
  let := finiteIntersectionOverDiagram_isAffine U p hU s
  apply (cancel_epi (finiteIntersectionSectionSpecIso U p hU s).hom).mp
  simpa [finiteIntersectionSectionSpecIso, finiteIntersectionSectionDiagram,
    finiteIntersectionOverDiagram, finiteIntersectionSchemeDiagram,
    finiteIntersectionOpenDiagram, affineBaseSectionFunctor] using (affineBaseSectionsSpecIso_over A
    ((finiteIntersectionOverDiagram U p).obj (.op s))).symm

/-- The actual diagonal chart is a closed immersion in tensor-product coordinates. -/
theorem finiteIntersectionSectionDiagram_product_closedImmersion (s t : NonemptyChartSet ι) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap
      (((finiteIntersectionSectionDiagram U p).map
        (homOfLE (le_unionChartSet_left s t))).hom)
      (((finiteIntersectionSectionDiagram U p).map
        (homOfLE (le_unionChartSet_right s t))).hom)).toRingHom)) := by
  exact affineProductMap_isClosedImmersion_of_isPullback _ _ p _ _
    (finiteIntersectionSectionDiagram_pair_isPullback U p hU s t)
    (by simpa only [Category.assoc] using finiteIntersectionSectionSpecIso_inv_over U p hU s)
    (by simpa only [Category.assoc] using finiteIntersectionSectionSpecIso_inv_over U p hU t)

end FLT.Mazur.Approximation
