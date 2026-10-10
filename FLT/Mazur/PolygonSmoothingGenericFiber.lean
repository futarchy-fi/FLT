/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingUnitParameter
public import FLT.Mazur.PolygonSmoothingBaseChange
public import FLT.Mazur.MultiplicativeGroupDimension

/-!
# Actual punctured-base fibers of the arithmetic node model

The original base-change square is smooth after making the parameter a unit.
Its relative dimension is one, including over a fraction field at a nonzero parameter.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonSmoothing

universe u

variable (R : Type u) [CommRing R]

/-- The original punctured left branch has relative dimension one. -/
theorem leftBranchOpen_relativeDimension (t : R) :
    SmoothOfRelativeDimension 1 (leftBranchOpen R t ≫ chartStructure R t) := by
  rw [leftBranchOpen_base]
  exact MultiplicativeGroupDimension.dimension R

/-- A unit-parameter arithmetic node chart is a smooth relative curve. -/
theorem chartStructure_relativeDimension_of_isUnit {t : R} (ht : IsUnit t) :
    SmoothOfRelativeDimension 1 (chartStructure R t) := by
  let _ := leftBranchOpen_isIso R ht
  let _ := leftBranchOpen_relativeDimension R t
  have he : chartStructure R t =
      inv (leftBranchOpen R t) ≫ (leftBranchOpen R t ≫ chartStructure R t) := by simp
  rw [he]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The actual coefficient pullback is a smooth curve when the parameter becomes a unit. -/
theorem chartBaseChange_relativeDimension (t : R) (ht : IsUnit (algebraMap R S t)) :
    SmoothOfRelativeDimension 1
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S))) (chartStructure R t)) := by
  let _ := chartStructure_relativeDimension_of_isUnit S ht
  have he : pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (chartStructure R t) =
      (chartBaseChangeIso R S t).hom ≫ chartStructure S (algebraMap R S t) := by
    rw [← chartBaseChangeIso_inv_fst, Iso.hom_inv_id_assoc]
  rw [he]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

/-- Inverting the original parameter makes the actual base-changed local model smooth. -/
theorem chartBaseChange_away_relativeDimension (t : R) [IsLocalization.Away t S] :
    SmoothOfRelativeDimension 1
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S))) (chartStructure R t)) :=
  chartBaseChange_relativeDimension R S t (IsLocalization.Away.algebraMap_isUnit t)

/-- Every nonzero-parameter fraction-field fiber of the original model is a smooth curve. -/
theorem chartBaseChange_fraction_relativeDimension
    (F : Type u) [Field F] [Algebra R F] [IsFractionRing R F] {t : R} (ht : t ≠ 0) :
    SmoothOfRelativeDimension 1
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R F))) (chartStructure R t)) := by
  apply chartBaseChange_relativeDimension
  apply isUnit_iff_ne_zero.mpr
  simpa only [map_zero] using (IsFractionRing.injective R F).ne ht

end FLT.Mazur.PolygonSmoothing
