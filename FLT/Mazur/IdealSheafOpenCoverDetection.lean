/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIdealSheafCoverComparison

/-!
# Detecting full ideal equalities and containments on arbitrary open covers

Refining each covering scheme by its affine cover detects full ideal sheaves.
The resulting containment criterion applies to arbitrary pulled-back Hilbert
chart covers, without any affineness hypothesis on their intersections.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace FLT.Mazur.BaseAdicThickening

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} (C : X.OpenCover)

/-- Any open cover detects equality of full ideal sheaves by affine refinement. -/
theorem idealSheaf_ext_of_openCover {J K : X.IdealSheafData}
    (h : ∀ i, J.comap (C.f i) = K.comap (C.f i)) : J = K := by
  let D := C.bind fun i ↦ (C.X i).affineOpenCover.openCover
  let _ : ∀ j, IsAffine (D.X j) := fun j ↦
    inferInstanceAs (IsAffine (Spec ((C.X j.1).affineOpenCover.X j.2)))
  apply idealSheaf_ext_of_affineCover D
  rintro ⟨i, j⟩
  change J.comap ((C.X i).affineOpenCover.f j ≫ C.f i) =
    K.comap ((C.X i).affineOpenCover.f j ≫ C.f i)
  rw [comap_comp, comap_comp, h i]

/-- An arbitrary open cover detects full containment, including nilpotent equations. -/
theorem idealSheaf_le_of_openCover {J K : X.IdealSheafData}
    (h : ∀ i, J.comap (C.f i) ≤ K.comap (C.f i)) : J ≤ K := by
  apply sup_eq_right.mp
  apply idealSheaf_ext_of_openCover C
  intro i
  rw [comap_sup, sup_eq_right.mpr (h i)]

/-- Full ideal containment is equivalent to containment after every covering restriction. -/
theorem idealSheaf_le_iff_openCover (J K : X.IdealSheafData) :
    J ≤ K ↔ ∀ i, J.comap (C.f i) ≤ K.comap (C.f i) :=
  ⟨fun h i ↦ comap_mono (C.f i) h, idealSheaf_le_of_openCover C⟩

/-- Vanishing of a full ideal sheaf is detected by every arbitrary open cover. -/
theorem idealSheaf_eq_bot_iff_openCover (J : X.IdealSheafData) :
    J = ⊥ ↔ ∀ i, J.comap (C.f i) = ⊥ := by
  constructor
  · intro h i
    rw [h, comap_bot]
  · intro h
    apply idealSheaf_ext_of_openCover C
    intro i
    rw [h, comap_bot]

end FLT.Mazur.BaseAdicThickening
