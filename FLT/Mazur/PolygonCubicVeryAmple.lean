/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicPointSeparation
public import FLT.Mazur.PolygonCubicOOnePullback
public import FLT.Mazur.DivisorPowerVeryAmple

/-!
# Very ampleness of the polygon cubic divisor line

The proved closed immersion, its structural-map equation and the actual
hyperplane pullback comparison give a very ample presentation. Transport
along the divisor-power isomorphism supplies the required tensor cube.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open FCurve FCurve.ModuleLineBundleTensorPullback PolygonPinching PolygonPowerNodeEndpoints
open ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- The actual cubic map presents the cubic divisor line as a hyperplane pullback. -/
def cubicVeryAmplePresentation : VeryAmplePresentation C.hom (polygonLine K n hn p q h a 3) where
  dimension := n * 3 + 1
  embedding := cubicProjectiveMorphism K n hn p q h a
  isClosedImmersion := cubicProjectiveMorphism_isClosedImmersion K n hn p q h a
  «over» := cubicProjectiveMorphism_baseProjection K n hn p q h a
  coefficientIso := (cubicProjectiveOOneIso K n hn p q h a).symm

/-- The cubic divisor line is relatively very ample on every affine base open. -/
theorem cubic_relativeVeryAmple : RelativeVeryAmple C.hom (polygonLine K n hn p q h a 3) := by
  let := PolygonProper.proper K n hn p q h
  let := cubicProjectiveMorphism_isClosedImmersion K n hn p q h a
  have he : cubicProjectiveMorphism K n hn p q h a ≫ baseProjection K _ =
      C.hom ≫ 𝟙 _ := by simp [cubicProjectiveMorphism_baseProjection]
  exact (relativeVeryAmple_pullbackOOne C.hom (𝟙 _) _ he).of_iso
    (cubicProjectiveOOneIso K n hn p q h a).symm

/-- A closed presentation for the tensor cube of the actual marked divisor line. -/
def divisorTensorCubePresentation : VeryAmplePresentation C.hom
    (tensorPower (divisorLineBundle (PolygonBoundaryDivisor.ideal K n p a)
      (PolygonBoundaryDivisor.cartier K n p hn q h a).1) 3) :=
  (cubicVeryAmplePresentation K n hn p q h a).ofIso
    (divisorLineBundlePowerIso (PolygonBoundaryDivisor.cartier K n p hn q h a).1 3)

/-- The tensor cube, with the exact divisor sheaf coefficients, is relatively very ample. -/
theorem divisor_tensorCube_relativeVeryAmple : RelativeVeryAmple C.hom
    (tensorPower (divisorLineBundle (PolygonBoundaryDivisor.ideal K n p a)
      (PolygonBoundaryDivisor.cartier K n p hn q h a).1) 3) :=
  (cubic_relativeVeryAmple K n hn p q h a).of_iso
    (divisorLineBundlePowerIso (PolygonBoundaryDivisor.cartier K n p hn q h a).1 3)

/-- The marked polygon divisor has an explicitly proved positive very ample power. -/
theorem exists_divisor_relativeVeryAmple_power : ∃ m > 0, RelativeVeryAmple C.hom
    (tensorPower (divisorLineBundle (PolygonBoundaryDivisor.ideal K n p a)
      (PolygonBoundaryDivisor.cartier K n p hn q h a).1) m) :=
  ⟨3, by decide, divisor_tensorCube_relativeVeryAmple K n hn p q h a⟩

end FLT.Mazur.PolygonCubicSections
