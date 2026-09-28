/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegralBase
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Inputs for the two-cusp argument

These are the consumer contracts of `docs/MAZUR_CONTRACTS.md`, expressed using
the section and point operations of `OverPoints`. They specify supplied data
and propositions about it; they do not construct modular curves or quotients.

In an arithmetic construction, `IntegralData.generic` must be the canonical
map `IntegralBase.generic`, and `primePoint` must come from the coarse moduli
interpretation. The quotient must be the integral extension of Abel–Jacobi
followed by the Eisenstein quotient. Those construction obligations remain
separate from the conditional diagram chase.

Source: Mazur, *Modular curves and the Eisenstein ideal* (1977), III §5,
pp. 159–160.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped WeierstrassCurve.Affine

namespace FLT.Mazur

/-- An elliptic curve with a specified rational point of order `p`. -/
structure PrimePoint (p : ℕ) where
  /-- The rational Weierstrass curve. -/
  curve : WeierstrassCurve ℚ
  /-- Nonsingularity of the curve. -/
  elliptic : curve.IsElliptic
  /-- The chosen rational point. -/
  point : (curve⁄ℚ).Point
  /-- The chosen point has order `p`. -/
  order : addOrderOf point = p

/-- Integral curve data, with two cusp sections and a supplied moduli assignment. -/
structure IntegralData (p : ℕ) where
  /-- The integral curve over the localized integer base. -/
  X : Over (Base p)
  /-- The specified map from the rational spectrum to the base. -/
  generic : Spec (CommRingCat.of ℚ) ⟶ Base p
  /-- The cusp section labelled zero. -/
  cuspZero : Sections X
  /-- The cusp section labelled infinity. -/
  cuspInfinity : Sections X
  /-- The supplied assignment from rational level structures to curve points. -/
  primePoint : PrimePoint p → Points X generic

/-- Restrict a section along the generic map supplied by the integral data. -/
def genericSection {p : ℕ} (D : IntegralData p) (x : Sections D.X) :
    Points D.X D.generic :=
  Sections.restrict D.generic x

/-- An integral target and a projection defined over the same base. -/
structure QuotientData {p : ℕ} (D : IntegralData p) where
  /-- The integral quotient target over the same base. -/
  A : Over (Base p)
  /-- The extended Abel–Jacobi map followed by the quotient projection. -/
  projection : D.X ⟶ A

/-- The projection on points over the specified generic map. -/
def onGeneric {p : ℕ} {D : IntegralData p} (Q : QuotientData D) :
    Points D.X D.generic → Points Q.A D.generic :=
  Points.map Q.projection

/-- The projected generic cusp points are distinct. -/
def G2Cusps {p : ℕ} {D : IntegralData p} (Q : QuotientData D) : Prop :=
  onGeneric Q (genericSection D D.cuspZero) ≠
    onGeneric Q (genericSection D D.cuspInfinity)

/-- Specialization is injective on all target sections at each allowed prime.
Producing this input requires the full torsion specialization argument,
including residue-characteristic-primary torsion. -/
def G2Specialization {p : ℕ} {D : IntegralData p} (Q : QuotientData D) : Prop :=
  ∀ (q : ℕ), q.Prime → q ≠ 2 → q ≠ p →
    ∀ s : Spec (CommRingCat.of (ZMod q)) ⟶ Base p,
      Function.Injective (fun a : Sections Q.A => s ≫ a.left)

end FLT.Mazur
