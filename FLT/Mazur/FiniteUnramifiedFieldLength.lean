/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFieldRankLength
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Etale.Field

/-!
# Length of finite unramified geometric schemes

Over a field, a finite formally unramified scheme is etale and reduced.
Over a separably closed field, its actual global section algebra is a product
of copies of the field, so its length equals its number of underlying points.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FCurve

universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [IsFinite f] [FormallyUnramified f]

/-- Finite formally unramified schemes over a field are etale. -/
theorem finiteUnramifiedField_etale : Etale f :=
  Etale.of_formallyUnramified_of_flat f

/-- The original scalar map on global sections is an etale ring map. -/
theorem finiteUnramifiedField_scalar_etale : (structureScalarMap f).Etale := by
  let _ : IsAffine X := isAffine_of_isAffineHom f
  let _ := finiteUnramifiedField_etale f
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (.of k)).inv))
    (HasRingHomProperty.appTop (P := @Etale) f inferInstance)

include f in
/-- No nilpotents remain in the actual scheme, not just in its point set. -/
theorem finiteUnramifiedField_reduced : IsReduced X := by
  let _ : IsAffine X := isAffine_of_isAffineHom f
  let _ := (structureScalarMap f).toAlgebra
  let _ : Algebra.Etale k Γ(X, ⊤) := finiteUnramifiedField_scalar_etale f
  let _ : _root_.IsReduced Γ(X, ⊤) :=
    Algebra.FormallyUnramified.isReduced_of_field k _
  exact isReduced_of_isAffine_isReduced X

/-- Geometric point count equals actual field length for a finite unramified scheme. -/
theorem finiteUnramifiedField_length_eq_card [IsSepClosed k] :
    finiteSchemeLength f = Nat.card X := by
  let _ : IsAffine X := isAffine_of_isAffineHom f
  let _ := (structureScalarMap f).toAlgebra
  let _ : Algebra.Etale k Γ(X, ⊤) := finiteUnramifiedField_scalar_etale f
  let _ : Module.Finite k Γ(X, ⊤) := structureScalarMap_finite f
  let _ : IsArtinianRing Γ(X, ⊤) := isArtinian_of_tower k inferInstance
  let _ : Fintype (PrimeSpectrum Γ(X, ⊤)) := Fintype.ofFinite _
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed k Γ(X, ⊤)
  have hc : Module.finrank k Γ(X, ⊤) = Nat.card (PrimeSpectrum Γ(X, ⊤)) := by
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi]
    simp
  calc
    finiteSchemeLength f = Module.finrank k Γ(X, ⊤) := (scalarH0Equiv f).finrank_eq
    _ = Nat.card (PrimeSpectrum Γ(X, ⊤)) := hc
    _ = Nat.card X := (Nat.card_congr X.isoSpec.hom.homeomorph.toEquiv).symm

/-- The finite-flat rank over a separably closed field equals the number of points. -/
theorem finiteUnramifiedField_rank_eq_card [IsSepClosed k] (s : Spec (.of k)) :
    f.finrank s = Nat.card X := by
  rw [finrank_eq_finiteSchemeLength, finiteUnramifiedField_length_eq_card]

end FLT.Mazur.FCurve
