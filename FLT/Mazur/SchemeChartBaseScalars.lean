/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Base scalar coordinates on a spectrum chart

A chart over an affine base retains the original base scalar map, even when
its sections are reached through a specified ambient open and preimage equality.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.SchemeChartBaseScalars

/-- Restricting a base scalar through an ambient open recovers the specified chart ring map. -/
lemma chart_appLE {X : Scheme.{u}} (R S : CommRingCat.{u})
    (p : X ⟶ Spec R) (i : Spec S ⟶ X) (a : R ⟶ S)
    (h : i ≫ p = Spec.map a) (W : X.Opens) (hi : i ⁻¹ᵁ W = ⊤) :
    (Scheme.ΓSpecIso R).inv ≫ p.appLE ⊤ W (by simp) ≫
        i.appLE W ⊤ (le_of_eq hi.symm) =
      a ≫ (Scheme.ΓSpecIso S).inv := by
  rw [Scheme.Hom.appLE_comp_appLE, h]
  change (Scheme.ΓSpecIso R).inv ≫ (Spec.map a).appTop = _
  exact (Scheme.ΓSpecIso_inv_naturality a).symm

end FLT.Mazur.SchemeChartBaseScalars
