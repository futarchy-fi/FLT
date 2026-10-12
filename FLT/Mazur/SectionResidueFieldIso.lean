/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Sections preserve the residue fields of their base points

A section gives a split residue-field homomorphism. A field homomorphism is
injective, and its section equation supplies surjectivity, without any
reducedness or closed-immersion assumption on the base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {X S : Scheme.{u}} (p : X ⟶ S) (s : S ⟶ X) (hs : s ≫ p = 𝟙 S)

include p hs in
/-- The residue map of an actual section is an isomorphism at every base point. -/
theorem section_residueFieldMap_isIso (a : S) : IsIso (s.residueFieldMap a) := by
  have h : IsIso ((s ≫ p).residueFieldMap a) := by
    exact (congrArg (fun k : S ⟶ S ↦ IsIso (k.residueFieldMap a)) hs).mpr inferInstance
  have hb := (ConcreteCategory.bijective_of_isIso ((s ≫ p).residueFieldMap a)).surjective
  rw [Scheme.residueFieldMap_comp] at hb
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ⟨(s.residueFieldMap a).hom.injective, Function.Surjective.of_comp hb⟩

end FLT.Mazur.FCurve
