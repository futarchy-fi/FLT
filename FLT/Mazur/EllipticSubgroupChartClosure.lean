/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticIntegralChartEvaluation
public import FLT.Mazur.AffineGenericClosure
public import Mathlib.Algebra.Algebra.Pi

/-!
# Affine chart closures of actual elliptic subgroups

For a subgroup of the generic elliptic point group, take the points lying in
one projective chart and evaluate its integral coordinate algebra at those
points. The kernel quotient is the concrete affine schematic closure. This
constructs its coordinate map and proves flatness; finiteness and compatible
Hopf operations are separate obligations.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.EllipticSubgroupChart

open WeierstrassIntegralChart WeierstrassCurve.Projective

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) (j : Fin 3)

/-- Actual generic subgroup points lying in the selected projective chart. -/
def Index := {P : H // ((primitiveLift A W P.1).coords j : K) ≠ 0}

/-- The generic normalizing unit at a point in the selected chart. -/
def denominator (P : Index A W H j) : Kˣ :=
  Units.mk0 ((primitiveLift A W P.1.1).coords j : K) P.2

/-- Generic coordinates, normalized at j; they need not all be integral. -/
def coordinates (P : Index A W H j) (i : Fin 3) : K :=
  (↑(denominator A W H j P)⁻¹ : K) * (primitiveLift A W P.1.1).coords i

/-- The coordinate selected for normalization equals one. -/
@[simp] theorem coordinates_self (P : Index A W H j) : coordinates A W H j P j = 1 :=
  Units.inv_mul _

/-- These are solutions of the actual generic cubic. -/
theorem coordinates_equation (P : Index A W H j) :
    (W.map (algebraMap A K)).toProjective.Equation (coordinates A W H j P) := by
  apply ((W.map (algebraMap A K)).toProjective.equation_smul _
    (denominator A W H j P)⁻¹.isUnit).mpr
  exact ((primitiveLift A W P.1.1).equation A W).map (algebraMap A K)

/-- The normalized generic coordinates represent the original subgroup point. -/
theorem coordinates_represents (P : Index A W H j) :
    (⟦coordinates A W H j P⟧ : PointClass K) = P.1.1.point := by
  refine Eq.trans ?_ (primitiveLift A W P.1.1).represents
  exact Quotient.sound ⟨(denominator A W H j P)⁻¹, rfl⟩

/-- The concrete chart map into the split algebra of generic subgroup points. -/
def coordinateMap : Coordinate W j →ₐ[A] (Index A W H j → K) :=
  AlgHom.pi fun P => evaluation W j (coordinates A W H j P)
    (coordinates_equation A W H j P) (coordinates_self A W H j P)

/-- Each universal coordinate evaluates to the actual subgroup coordinate function. -/
@[simp] theorem coordinateMap_coord (i : Fin 3) (P : Index A W H j) :
    coordinateMap A W H j (coord W j i) P = coordinates A W H j P i :=
  evaluation_coord W j (coordinates A W H j P)
    (coordinates_equation A W H j P) (coordinates_self A W H j P) i

/-- The coordinate algebra of the subgroup's closure in this integral chart. -/
abbrev Closure := AffineGenericClosure.Coordinate (coordinateMap A W H j)

/-- The actual chart closure has no valuation-ring torsion. -/
theorem closure_isTorsionFree : Module.IsTorsionFree A (Closure A W H j) :=
  AffineGenericClosure.isTorsionFree K (coordinateMap A W H j)

/-- Over a DVR the actual chart closure is flat. -/
theorem closure_flat [IsDedekindDomain A] : Module.Flat A (Closure A W H j) :=
  AffineGenericClosure.flat K (coordinateMap A W H j)

/-- Distinct chart indices have distinct normalized coordinate vectors. -/
theorem coordinates_injective : Function.Injective (coordinates A W H j) := by
  intro P Q h
  apply Subtype.ext
  apply Subtype.ext
  apply Point.ext
  exact (coordinates_represents A W H j P).symm.trans
    ((congrArg Quotient.mk'' h).trans (coordinates_represents A W H j Q))

end FLT.Mazur.EllipticSubgroupChart
