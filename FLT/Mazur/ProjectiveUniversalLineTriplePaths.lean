/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveUniversalChartLineOverlap
public import FLT.Mazur.ProjectiveTwistCocycle

/-!
# Agreement of chart paths to homogeneous triple overlaps

The two routes from each standard chart to the actual triple homogeneous
localization agree as ring maps. Consequently the extended universal lines
are independent of the intermediate pairwise intersection.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) [CommRing R] (ι : Type u)
/-- The two restriction routes from the first chart to the triple overlap agree. -/
lemma chartTriple_first (i j k : ι) :
    (toTriple₁₂ R ι i j k).comp (chartOverlapLeft R ι i j).toRingHom =
      (toTriple₁₃ R ι i j k).comp (chartOverlapLeft R ι i k).toRingHom := by
  apply chartRing_hom_ext
  · intro r
    dsimp only [RingHom.comp_apply, chartOverlapLeft, chartOverlapRight, toOverlap,
      chartScalars, toTriple₁₂, toTriple₂₃, toTriple₁₃]
    simp only [awayMap_fromZeroRingHom]
  · intro a
    dsimp only [RingHom.comp_apply, chartOverlapLeft, chartOverlapRight, toOverlap, coordinate,
      toTriple₁₂, toTriple₂₃, toTriple₁₃]
    simp only [awayMap_mk]
    apply val_injective
    simp only [Away.val_mk, pow_one, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul]
    ring

/-- The two restriction routes from the middle chart to the triple overlap agree. -/
lemma chartTriple_middle (i j k : ι) :
    (toTriple₁₂ R ι i j k).comp (chartOverlapRight R ι i j).toRingHom =
      (toTriple₂₃ R ι i j k).comp (chartOverlapLeft R ι j k).toRingHom := by
  apply chartRing_hom_ext
  · intro r
    dsimp only [RingHom.comp_apply, chartOverlapLeft, chartOverlapRight, toOverlap,
      chartScalars, toTriple₁₂, toTriple₂₃, toTriple₁₃]
    simp only [awayMap_fromZeroRingHom]
  · intro a
    dsimp only [RingHom.comp_apply, chartOverlapLeft, chartOverlapRight, toOverlap, coordinate,
      toTriple₁₂, toTriple₂₃, toTriple₁₃]
    simp only [awayMap_mk]
    apply val_injective
    simp only [Away.val_mk, pow_one, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul]
    ring

/-- The two restriction routes from the last chart to the triple overlap agree. -/
lemma chartTriple_last (i j k : ι) :
    (toTriple₂₃ R ι i j k).comp (chartOverlapRight R ι j k).toRingHom =
      (toTriple₁₃ R ι i j k).comp (chartOverlapRight R ι i k).toRingHom := by
  apply chartRing_hom_ext
  · intro r
    dsimp only [RingHom.comp_apply, chartOverlapLeft, chartOverlapRight, toOverlap,
      chartScalars, toTriple₁₂, toTriple₂₃, toTriple₁₃]
    simp only [awayMap_fromZeroRingHom]
  · intro a
    dsimp only [RingHom.comp_apply, chartOverlapLeft, chartOverlapRight, toOverlap, coordinate,
      toTriple₁₂, toTriple₂₃, toTriple₁₃]
    simp only [awayMap_mk]
    apply val_injective
    simp only [Away.val_mk, pow_one, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul]
    ring

open NormalizedSectionLine

/-- Any affine refinement preserves equality of the actual universal line submodules. -/
lemma universalChartLine_refine_val {S : Type u} [CommRing S] (i j : ι)
    (φ : overlapRing R ι i j →+* S) :
    (baseChange (φ.comp (chartOverlapLeft R ι i j).toRingHom) i
        (universalChartLine R ι i)).val =
      (baseChange (φ.comp (chartOverlapRight R ι i j).toRingHom) j
        (universalChartLine R ι j)).val := by
  rw [← baseChange_comp, ← baseChange_comp]
  exact baseChange_val_eq φ i j _ _ (universalChartLine_overlap_val R ι i j)

/-- The first actual chart line on the homogeneous triple intersection. -/
abbrev universalTripleLine₁ (i j k : ι) : Chart (tripleRing R ι i j k) ι i :=
  baseChange ((toTriple₁₂ R ι i j k).comp (chartOverlapLeft R ι i j).toRingHom) i
    (universalChartLine R ι i)

/-- The middle actual chart line on the same homogeneous triple intersection. -/
abbrev universalTripleLine₂ (i j k : ι) : Chart (tripleRing R ι i j k) ι j :=
  baseChange ((toTriple₁₂ R ι i j k).comp (chartOverlapRight R ι i j).toRingHom) j
    (universalChartLine R ι j)

/-- The last actual chart line on the same homogeneous triple intersection. -/
abbrev universalTripleLine₃ (i j k : ι) : Chart (tripleRing R ι i j k) ι k :=
  baseChange ((toTriple₂₃ R ι i j k).comp (chartOverlapRight R ι j k).toRingHom) k
    (universalChartLine R ι k)

/-- The first two chart lines coincide on the actual triple localization. -/
lemma universalTripleLine_val₁₂ (i j k : ι) :
    (universalTripleLine₁ R ι i j k).val = (universalTripleLine₂ R ι i j k).val :=
  universalChartLine_refine_val R ι i j _

/-- The second overlap recovers those same chart lines, independently of the route. -/
lemma universalTripleLine_val₂₃ (i j k : ι) :
    (universalTripleLine₂ R ι i j k).val = (universalTripleLine₃ R ι i j k).val := by
  dsimp only [universalTripleLine₂, universalTripleLine₃]
  rw [chartTriple_middle]
  exact universalChartLine_refine_val R ι j k _

/-- The outer overlap recovers the same first and last submodules. -/
lemma universalTripleLine_val₁₃ (i j k : ι) :
    (universalTripleLine₁ R ι i j k).val = (universalTripleLine₃ R ι i j k).val := by
  dsimp only [universalTripleLine₁, universalTripleLine₃]
  rw [chartTriple_first, chartTriple_last]
  exact universalChartLine_refine_val R ι i k _

end FLT.Mazur.ProjectiveSpace
