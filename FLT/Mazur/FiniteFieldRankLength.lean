/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteSchemeLength
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Finite morphism rank and actual field length

Over a field the geometric finite-flat rank equals the dimension of the actual
structure-sheaf H⁰. This identifies the scheme rank with the cohomological length
used to compute effective-divisor degree.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsFinite f]

/-- Over a field, rank agrees with the actual structure-cohomology length. -/
theorem finrank_eq_finiteSchemeLength (s : Spec (CommRingCat.of k)) :
    f.finrank s = finiteSchemeLength f := by
  let _ : IsAffine X := isAffine_of_isAffineHom f
  let _ := (structureScalarMap f).toAlgebra
  let _ : Module.Finite k Γ(X, ⊤) := structureScalarMap_finite f
  have he : f = X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (structureScalarMap f)) := by
    simp only [structureScalarMap, CommRingCat.ofHom_hom, Spec.map_comp]
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality]
    simp [Scheme.isoSpec_Spec_hom]
  let _ : IsFinite (Spec.map (CommRingCat.ofHom (structureScalarMap f))) := by
    rw [IsFinite.SpecMap_iff]
    exact structureScalarMap_finite f
  conv_lhs => rw [he, Scheme.Hom.finrank_comp_left_of_isIso]
  rw [Scheme.Hom.finrank_SpecMap_eq_finrank
    (f := CommRingCat.ofHom (structureScalarMap f)) (structureScalarMap_finite f)
    (show (structureScalarMap f).Flat from inferInstanceAs (Module.Flat k Γ(X, ⊤)))]
  change Module.rankAtStalk Γ(X, ⊤) s = _
  rw [Module.rankAtStalk_eq_finrank_of_free]
  exact (scalarH0Equiv f).finrank_eq.symm

omit [IsFinite f] in
/-- A scheme isomorphic to the base field has actual length one. -/
theorem finiteSchemeLength_of_isIso [IsIso f] : finiteSchemeLength f = 1 := by
  rw [← finrank_eq_finiteSchemeLength f (IsLocalRing.closedPoint k)]
  exact congrFun (Scheme.Hom.finrank_eq_one_of_isIso f) _

end FLT.Mazur.FCurve
