/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteAlgebraSpectrumCard
public import FLT.Mazur.FiniteFieldRankLength
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# Finite-flat degree bounds actual fiber point counts

The scheme fiber over its original residue field has the same points as
the topological fiber. Chinese remaindering bounds their number by the
dimension of its functions, and finite-flat base change identifies this
dimension with the original degree. Nonsplit and nonreduced fibers are allowed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteFlatFiberCard
open FCurve
set_option backward.isDefEq.respectTransparency false
universe u

/-- A finite scheme over a field has at most its degree many underlying points. -/
theorem card_le_finrank_over_field {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsFinite f] (s : Spec (.of K)) :
    Nat.card X ≤ f.finrank s := by
  let _ : IsAffine X := isAffine_of_isAffineHom f
  let _ := (structureScalarMap f).toAlgebra
  let _ : Module.Finite K Γ(X, ⊤) := structureScalarMap_finite f
  rw [finrank_eq_finiteSchemeLength f s]
  calc
    Nat.card X = Nat.card (PrimeSpectrum Γ(X, ⊤)) :=
      Nat.card_congr X.isoSpec.hom.homeomorph.toEquiv
    _ ≤ Module.finrank K Γ(X, ⊤) :=
      FiniteAlgebraSpectrumCard.card_primeSpectrum_le_finrank K Γ(X, ⊤)
    _ = finiteSchemeLength f := (scalarH0Equiv f).finrank_eq.symm

/-- Actual fiber cardinality is bounded by finite-flat degree at the original base point. -/
theorem fiber_ncard_le_finrank {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f]
    (y : Y) : (f ⁻¹' {y}).ncard ≤ f.finrank y := by
  let _ : IsFinite (f.fiberToSpecResidueField y) :=
    inferInstanceAs (IsFinite (pullback.snd f (Y.fromSpecResidueField y)))
  have h := card_le_finrank_over_field (f.fiberToSpecResidueField y)
    (IsLocalRing.closedPoint (Y.residueField y))
  change Nat.card (f.fiber y) ≤
    (pullback.snd f (Y.fromSpecResidueField y)).finrank _ at h
  rw [Scheme.Hom.finrank_pullback_snd, Scheme.fromSpecResidueField_apply] at h
  change Nat.card (f ⁻¹' {y}) ≤ _
  rwa [← Nat.card_congr (f.fiberHomeo y).toEquiv]

end FLT.Mazur.FiniteFlatFiberCard
