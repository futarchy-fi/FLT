/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveUniversalChartLine

/-!
# Actual universal chart lines agree on homogeneous overlaps

Both coordinate submodules are extended along the genuine homogeneous
localization maps. Recharting by the homogeneous ratio identifies them.
The resulting isomorphism between the actual pullback line sheaves preserves
the inclusions after the canonical ambient coefficient comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
open NormalizedSectionLine
variable (R : Type u) [CommRing R] (ι : Type u)

/-- The universal generator's other coordinate is the actual homogeneous ratio unit. -/
lemma universalChartLine_overlap_unit (i j : ι) :
    generator (overlapRing R ι i j) ι i
        (baseChange (chartOverlapLeft R ι i j).toRingHom i (universalChartLine R ι i)) j =
      (ratioUnit R ι i j : overlapRing R ι i j) := by
  rw [generator_baseChange, universalChartLine_generator, ratioUnit_val]
  rfl

/-- The right universal chart line is the recharting of the left line on the actual overlap. -/
lemma universalChartLine_overlap_rechart (i j : ι) :
    rechart i j
        (baseChange (chartOverlapLeft R ι i j).toRingHom i (universalChartLine R ι i))
        (ratioUnit R ι i j) (universalChartLine_overlap_unit R ι i j) =
      baseChange (chartOverlapRight R ι i j).toRingHom j (universalChartLine R ι j) := by
  apply (tupleEquiv (overlapRing R ι i j) ι j).symm.injective
  apply Subtype.ext
  funext k
  change generator (overlapRing R ι i j) ι j _ k =
    generator (overlapRing R ι i j) ι j _ k
  rw [generator_rechart, generator_baseChange, generator_baseChange,
    universalChartLine_generator, universalChartLine_generator]
  change (↑(ratioUnit R ι i j)⁻¹ : overlapRing R ι i j) *
      chartOverlapLeft R ι i j (coordinate R ι i k) =
    chartOverlapRight R ι i j (coordinate R ι j k)
  rw [chartOverlap_coordinate]
  change (↑(ratioUnit R ι i j)⁻¹ : overlapRing R ι i j) *
      (chartOverlapRight R ι i j (coordinate R ι j k) * ↑(ratioUnit R ι i j)) = _
  rw [mul_left_comm, Units.inv_mul, mul_one]

/-- The two universal chart lines agree as actual submodules of the overlap coordinate module. -/
lemma universalChartLine_overlap_val (i j : ι) :
    (baseChange (chartOverlapLeft R ι i j).toRingHom i (universalChartLine R ι i)).val =
      (baseChange (chartOverlapRight R ι i j).toRingHom j (universalChartLine R ι j)).val :=
  congrArg Subtype.val (universalChartLine_overlap_rechart R ι i j)

/-- The sheaf overlap isomorphism is built between the two actual pullback line sheaves. -/
def universalChartLineOverlap (i j : ι) :
    (pullback (Spec.map (CommRingCat.ofHom (chartOverlapLeft R ι i j).toRingHom))).obj
        (universalChartLineSheaf R ι i) ≅
      (pullback (Spec.map (CommRingCat.ofHom (chartOverlapRight R ι i j).toRingHom))).obj
        (universalChartLineSheaf R ι j) :=
  universalChartLinePullback R ι i (chartOverlapLeft R ι i j).toRingHom ≪≫
    sheafChartChange i j _ _ (universalChartLine_overlap_val R ι i j) ≪≫
      (universalChartLinePullback R ι j (chartOverlapRight R ι i j).toRingHom).symm

attribute [local irreducible] universalChartLinePullback sheafChartChange
attribute [local irreducible] vectorSheafBaseChange Scheme.Modules.pullback

/-- The actual overlap map commutes with both inclusions in their common ambient sheaf. -/
lemma universalChartLineOverlap_inclusion [Finite ι] (i j : ι) :
    (universalChartLineOverlap R ι i j).hom ≫
        (pullback (Spec.map (CommRingCat.ofHom (chartOverlapRight R ι i j).toRingHom))).map
          (universalChartLineInclusion R ι j) ≫
        (vectorSheafBaseChange ι (chartOverlapRight R ι i j).toRingHom).hom =
      (pullback (Spec.map (CommRingCat.ofHom (chartOverlapLeft R ι i j).toRingHom))).map
          (universalChartLineInclusion R ι i) ≫
        (vectorSheafBaseChange ι (chartOverlapLeft R ι i j).toRingHom).hom := by
  rw [← universalChartLinePullback_inclusion, ← universalChartLinePullback_inclusion]
  simp only [universalChartLineOverlap, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, sheafChartChange_inclusion]

end FLT.Mazur.ProjectiveSpace
