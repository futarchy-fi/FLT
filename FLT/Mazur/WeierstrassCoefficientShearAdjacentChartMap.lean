/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearAdjacentFactor

/-!
# The whole adjacent conic open mapped into the next original tensor chart

Name the full map before substituting retained-family indices. This keeps
localization and tensor presentations sealed during indexed composition.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π (k + 1)) (e : Data W π (k + 1 + 1))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S (π ^ k) = 0) (hp : algebraMap R S π = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "g3" => And.left (coefficientShearAdjacent_coefficients hπ d e S hp)
local notation "g4" => And.left (And.right (coefficientShearAdjacent_coefficients hπ d e S hp))
local notation "E" => tensorShearConicBoundaryIso W (π ^ k) π
  d.b3 d.b4 d.b6 S r hs hp g3 g4 hr
local notation "x" => WeierstrassDilatation.x W (π ^ k * π) d.b3 d.b4 d.b6
local notation "t" => coord W (π ^ k) π d.b3 d.b4 d.b6 0
local notation "A" => Scheme.Spec.mapIso (Iso.op (RingEquiv.toCommRingCatIso
  (AlgEquiv.toRingEquiv (tensorOverlapEquiv W (π ^ k) π d.b3 d.b4 d.b6 S))))
local notation "B" => tensorAdjacentBoundaryIso hπ d e S
local notation "J" => coefficientShearAdjacentConicIso hπ d e S r hs hp hr

local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "C" => MiddleConicOpen U (algebraMap R S d.b6)
local notation "T" => ScalarExtension W (π ^ (k + 1)) π e.b3 e.b4 e.b6 S
local notation "i" => PrincipalOpenTensor.inclusion S
  (coord W (π ^ (k + 1)) π e.b3 e.b4 e.b6 2)

/-- The entire conic incidence open mapped by the genuine transition into the next tensor chart. -/
irreducible_def coefficientShearAdjacentConicToNext : Spec (.of C) ⟶ Spec (.of T) :=
  (J).hom ≫ i

/-- The named whole map still factors through both actual tensor boundary transitions. -/
@[reassoc] theorem coefficientShearAdjacentConicToNext_factor :
    coefficientShearAdjacentConicToNext hπ d e S r hs hp hr =
      (E).hom ≫ (A).hom ≫ (B).inv ≫ i := by
  rw [coefficientShearAdjacentConicToNext_def, coefficientShearAdjacentConicIso_factor]
  simp only [Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
