/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Supports of scheme maps factoring through a closed subscheme

A retained factorization puts every actual image point in the defining ideal's
support, without unfolding the scheme supplying that factorization.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.FCurve

/-- A specified factorization through a closed subscheme retains support membership. -/
theorem idealSupport_mem_of_factorization {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (e : Y ⟶ I.subscheme) (i : Y ⟶ X) (hi : e ≫ I.subschemeι = i) (y : Y) :
    i y ∈ I.support := by
  rw [← hi, Scheme.Hom.comp_apply, Scheme.IdealSheafData.subschemeι_apply]
  exact (e y).property

end FLT.Mazur.FCurve
