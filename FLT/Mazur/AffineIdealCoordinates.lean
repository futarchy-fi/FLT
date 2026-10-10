/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialFamilyFaithful

/-!
# Coordinate ideals of affine ideal sheaves

Taking global sections and the canonical spectrum identification recovers an
actual ring ideal. Both inverse laws retain the entire ideal sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace FLT.Mazur.BaseAdicThickening

/-- The ring ideal associated to an ideal sheaf on a spectrum. -/
def coordinateIdeal (A : CommRingCat.{u}) (J : (Spec A).IdealSheafData) : Ideal A :=
  (J.ideal ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso A).hom.hom

/-- Taking coordinates after sheafification returns the original full ring ideal. -/
theorem coordinateIdeal_baseIdeal (A : CommRingCat.{u}) (J : Ideal A) :
    coordinateIdeal A (baseIdeal A J) = J := by
  simp only [coordinateIdeal, baseIdeal_top, Ideal.map_map, ← CommRingCat.hom_comp,
    Iso.inv_hom_id, CommRingCat.hom_id, Ideal.map_id]

/-- Sheafifying the coordinate ideal returns the original full ideal sheaf. -/
theorem baseIdeal_coordinateIdeal (A : CommRingCat.{u}) (J : (Spec A).IdealSheafData) :
    baseIdeal A (coordinateIdeal A J) = J := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp only [baseIdeal_top, coordinateIdeal, Ideal.map_map, ← CommRingCat.hom_comp,
    Iso.hom_inv_id, CommRingCat.hom_id, Ideal.map_id]

/-- Actual coordinate ideals and ideal sheaves on a spectrum are equivalent. -/
def coordinateIdealEquiv (A : CommRingCat.{u}) : (Spec A).IdealSheafData ≃ Ideal A where
  toFun := coordinateIdeal A
  invFun := baseIdeal A
  left_inv := baseIdeal_coordinateIdeal A
  right_inv := coordinateIdeal_baseIdeal A

/-- Coordinate ideals commute with arbitrary scalar extension. -/
theorem coordinateIdeal_comap_specMap {A B : CommRingCat.{u}}
    (J : (Spec A).IdealSheafData) (f : A ⟶ B) :
    coordinateIdeal B (J.comap (Spec.map f)) = (coordinateIdeal A J).map f.hom := by
  rw [← baseIdeal_coordinateIdeal A J, baseIdeal_comap_specMap,
    coordinateIdeal_baseIdeal, coordinateIdeal_baseIdeal]

end FLT.Mazur.BaseAdicThickening
