/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealSheafRadicalOpen
public import FLT.Mazur.SmoothGeometricallyReduced
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Exact radical ideals under smooth scheme pullback

Smooth pullback preserves a radical ideal over a locally Noetherian base.
Thus invariant closed supports give equality of their actual defining ideals,
which can subsequently be raised to powers without losing nilpotent equations.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SmoothRadicalIdealSheaf
open Scheme.IdealSheafData
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme} [IsLocallyNoetherian Y]
  (I : Y.IdealSheafData) (f : X ⟶ Y) [Smooth f]

/-- The full pulled ideal is radical, even when the ambient base is nonreduced. -/
theorem comap_radical_eq_self (hI : I.radical = I) :
    (I.comap f).radical = I.comap f := by
  let _ := IdealSheafRadicalOpen.subscheme_isReduced I hI
  let _ := Approximation.geometricallyReduced_of_smooth f
  let _ : IsLocallyNoetherian I.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  let _ : IsReduced (I.comap f).subscheme :=
    isReduced_of_isOpenImmersion (I.comapIso f).hom
  rw [← ker_subschemeι (I.comap f)]
  exact IdealSheafRadicalOpen.ker_radical _

/-- Smooth endpoints with the same inverse closed support pull back identical equations. -/
theorem comap_eq_of_support {D : Scheme} (p q : D ⟶ Y) [Smooth p] [Smooth q]
    (hI : I.radical = I)
    (h : p ⁻¹' (I.support : Set Y) = q ⁻¹' (I.support : Set Y)) :
    I.comap p = I.comap q := by
  rw [← comap_radical_eq_self I p hI, ← comap_radical_eq_self I q hI,
    ← vanishingIdeal_support, ← vanishingIdeal_support]
  congr 1
  rw [support_comap, support_comap]
  ext x
  exact Set.ext_iff.mp h x

end FLT.Mazur.SmoothRadicalIdealSheaf
