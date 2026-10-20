/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatClosedComparison

/-!
# Whole ideal-sheaf equality from finite flat degree

Nested closed families of the same finite flat degree coincide as subschemes.
This applies to a possibly nonaffine ambient scheme over an affine base and
retains all nilpotents and multiplicities in the original ideal sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FCurve

universe u
variable {X S : Scheme.{u}} [IsAffine S]

/-- Containment and equal finite flat degree identify the entire ambient ideal sheaves. -/
theorem idealSheaf_eq_of_le_of_finiteLocallyFreeDegree (p : X ⟶ S)
    (I J : X.IdealSheafData) (h : I ≤ J) (d : ℕ)
    (hI : FiniteLocallyFreeDegree (I.subschemeι ≫ p) d)
    (hJ : FiniteLocallyFreeDegree (J.subschemeι ≫ p) d) : I = J := by
  let i := Scheme.IdealSheafData.inclusion h
  have hi : i ≫ I.subschemeι = J.subschemeι :=
    Scheme.IdealSheafData.inclusion_subschemeι h
  let _ : IsClosedImmersion i := IsClosedImmersion.of_comp i I.subschemeι
  let _ : IsIso i := isIso_closed_of_finiteLocallyFreeDegree
    (J.subschemeι ≫ p) (I.subschemeι ≫ p) i (by rw [← Category.assoc, hi]) d hJ hI
  rw [← I.ker_subschemeι, ← J.ker_subschemeι, ← hi, Scheme.Hom.ker_comp_of_isIso]

end FLT.Mazur.FCurve
