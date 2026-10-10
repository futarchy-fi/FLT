/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIdealCoordinates

/-!
# Exact affine ideal containment

Sheafifying coordinate ideals preserves and reflects the full order on
ideals. These tests retain nilpotents and apply to arbitrary quotient
ambient equations without reducedness or finite generation assumptions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace FLT.Mazur.BaseAdicThickening

/-- Sheafification preserves and reflects containment of full coordinate ideals. -/
theorem baseIdeal_le_iff (A : CommRingCat.{u}) (J K : Ideal A) :
    baseIdeal A J ≤ baseIdeal A K ↔ J ≤ K := by
  constructor
  · intro h
    have he := Ideal.map_mono (f := (Scheme.ΓSpecIso A).hom.hom)
      (h ⟨⊤, isAffineOpen_top _⟩)
    simpa only [baseIdeal_top, Ideal.map_map, ← CommRingCat.hom_comp,
      Iso.inv_hom_id, CommRingCat.hom_id, Ideal.map_id] using he
  · intro h
    apply le_of_isAffine
    rw [baseIdeal_top, baseIdeal_top]
    exact Ideal.map_mono h

/-- Full ideal containment on an affine spectrum is precisely coordinate ideal containment. -/
theorem coordinateIdeal_le_iff (A : CommRingCat.{u}) (J K : (Spec A).IdealSheafData) :
    coordinateIdeal A J ≤ coordinateIdeal A K ↔ J ≤ K := by
  rw [← baseIdeal_le_iff, baseIdeal_coordinateIdeal, baseIdeal_coordinateIdeal]

end FLT.Mazur.BaseAdicThickening
