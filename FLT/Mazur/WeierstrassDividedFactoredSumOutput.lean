/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFactoredSumCoordinates
public import FLT.Mazur.WeierstrassDividedOwnSumDepthOutput

/-!
# Whole sum-depth outputs retaining the quadratic quotient

The constructed factored coordinates satisfy the whole divided equation.
The resulting algebra map keeps the finite second-coefficient quotient
and the original coefficient morphism.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [Module.Flat R S] {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k l : ℕ}
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (dd : CommonBranchData d k) (ee : CommonBranchData e k) (z : Data W π (k + l))
  (b2 : R) (h2 : W.a₂ = π ^ k * b2)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "s" => algebraMap R S (π ^ k)
local notation "t" => algebraMap R S (π ^ (l - k))
local notation "x₁" => a (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "y₁" => a (y W (π ^ k) d.b3 d.b4 d.b6)
local notation "x₂" => c (x W (π ^ l) e.b3 e.b4 e.b6)
local notation "y₂" => c (y W (π ^ l) e.b3 e.b4 e.b6)
local notation "W'" => W.map (algebraMap R S)
variable (hc : IsUnit (a (y W (π ^ k) d.b3 d.b4 d.b6) +
    algebraMap R S W.a₁ * a (x W (π ^ k) d.b3 d.b4 d.b6) + algebraMap R S d.b3))
  (hd : IsUnit (c (y W (π ^ l) e.b3 e.b4 e.b6) +
    algebraMap R S W.a₁ * c (x W (π ^ l) e.b3 e.b4 e.b6) + algebraMap R S e.b3))
  (hxu : IsUnit (a (x W (π ^ k) d.b3 d.b4 d.b6) *
    c (x W (π ^ l) e.b3 e.b4 e.b6))) (i L : S)
local notation "q" => factoredCommonBranchOrdinate d dd b2 a hc
local notation "r" => factoredCommonBranchOrdinate e ee b2 c hd
local notation "b" => sumDepthIntercept 1 x₁ x₂ q r i

variable (hi : i * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) = 1)
  (hL : L * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) =
      a (y W (π ^ k) d.b3 d.b4 d.b6) -
        algebraMap R S (π ^ (l - k)) * c (y W (π ^ l) e.b3 e.b4 e.b6))

local notation "X" => factoredSumDepthX d e dd ee z b2 a c hc hd hxu i
local notation "Y" => factoredSumDepthY d e dd ee z b2 a c hc hd hxu i L

include hπ hkl h2 hi hL in
/-- The two computed sum-depth coordinates satisfy the entire target equation. -/
theorem factoredSumDepth_equation :
    Y ^ 2 + (algebraMap R S W.a₁ * X + algebraMap R S z.b3) * Y =
      algebraMap R S (π ^ (k + l)) * X ^ 3 + algebraMap R S W.a₂ * X ^ 2 +
        algebraMap R S z.b4 * X + algebraMap R S z.b6 := by
  apply equation_of_scaled W (π ^ (k + l)) z.b3 z.b4 z.b6
    z.factor3 z.factor4 z.factor6 (ownSumDepth_regular hπ) X Y
  rw [factoredSumDepthX_scale hπ d e hkl dd ee z b2 h2 a c hc hd hxu i L hi hL,
    factoredSumDepthY_scale hπ d e hkl dd ee z b2 h2 a c hc hd hxu i L hi hL]
  exact (WeierstrassCurve.Projective.equation_some ..).mpr
    (ownSumDepth_original_equation hπ d e hkl a c i L hi hL)

/-- The actual algebra map into the available sum-depth chart. -/
def factoredSumDepthOutput : Coordinate W (π ^ (k + l)) z.b3 z.b4 z.b6 →ₐ[R] S :=
  evaluation W (π ^ (k + l)) z.b3 z.b4 z.b6 X Y
    (factoredSumDepth_equation hπ d e hkl dd ee z b2 h2 a c hc hd hxu i L hi hL)

local notation "out" => factoredSumDepthOutput hπ d e hkl dd ee z b2 h2 a c hc hd hxu i L hi hL

/-- The target abscissa is exactly the constructed quotient. -/
@[simp] theorem factoredSumDepthOutput_x : out (x W (π ^ (k + l)) z.b3 z.b4 z.b6) = X :=
  evaluation_x ..

/-- The target ordinate is exactly the constructed quotient. -/
@[simp] theorem factoredSumDepthOutput_y : out (y W (π ^ (k + l)) z.b3 z.b4 z.b6) = Y :=
  evaluation_y ..

open AlgebraicGeometry CategoryTheory

/-- The same output as a morphism to the actual divided chart. -/
def factoredSumDepthLift : Spec (.of S) ⟶ chart z :=
  Spec.map (CommRingCat.ofHom (out).toRingHom)

/-- The constructed output preserves the original coefficient point. -/
@[reassoc] theorem factoredSumDepthLift_structure :
    factoredSumDepthLift hπ d e hkl dd ee z b2 h2 a c hc hd hxu i L hi hL ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap R (Coordinate W (π ^ (k + l)) z.b3 z.b4 z.b6))) =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) :=
  WeierstrassIntegralChart.specAlgHom_structure _

end FLT.Mazur.WeierstrassDividedDepth
