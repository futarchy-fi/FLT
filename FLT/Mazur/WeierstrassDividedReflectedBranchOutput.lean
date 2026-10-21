/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReflectedBranchCoordinates
public import FLT.Mazur.WeierstrassDividedOwnSumDepthOutput

/-!
# Actual reflected-depth output maps

The constructed reflected coordinates satisfy the entire divided equation.
This yields an algebra map and scheme output without a supplied output
point, including when the reflected-depth datum does not exist.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsLocalRing R] [Module.Flat R S] {W : WeierstrassCurve R} {π : R} {k l m : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π k) (e : Data W π l)
  (hkl : k ≤ l) (hl : 2 * l ≤ m) (hm : m ≤ k + 2 * l)
  (z : Data W π (m - k - l)) (h2 : W.a₂ = 0)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "s" => algebraMap R S (π ^ k)
local notation "t" => algebraMap R S (π ^ (l - k))
local notation "v" => algebraMap R S (π ^ (m - 2 * l))
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
local notation "q" => commonBranchOrdinate d (reflectedLeftBranchData D d hkl hl) a hc
local notation "r" => commonBranchOrdinate e (reflectedRightBranchData (k := k) D e hl) c hd
local notation "b" => sumDepthIntercept 1 x₁ x₂ q r i
local notation "C" => algebraMap R S (reflectedBranchConstant D d hkl hl)

local notation "X" => nodeReflectedX D d e hkl hl a c hc hd hxu i
local notation "Y" => nodeReflectedY D d e hkl hl z a c hc hd hxu i L
variable (hi : i * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) = 1)
  (hL : L * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) =
      a (y W (π ^ k) d.b3 d.b4 d.b6) -
        algebraMap R S (π ^ (l - k)) * c (y W (π ^ l) e.b3 e.b4 e.b6))

include hm h2 hi hL in
/-- The two computed reflected-depth coordinates satisfy the entire target equation. -/
theorem nodeReflected_equation :
    Y ^ 2 + (algebraMap R S W.a₁ * X + algebraMap R S z.b3) * Y =
      algebraMap R S (π ^ (m - k - l)) * X ^ 3 + algebraMap R S W.a₂ * X ^ 2 +
        algebraMap R S z.b4 * X + algebraMap R S z.b6 := by
  have hreg : IsRegular (algebraMap R S (π ^ (m - k - l))) :=
    WeierstrassIntegralChart.flatRingHom_isRegular _
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
      (isRegular_iff_ne_zero.mpr (pow_ne_zero _ D.uniformizer_ne_zero))
  apply equation_of_scaled W (π ^ (m - k - l)) z.b3 z.b4 z.b6
    z.factor3 z.factor4 z.factor6 hreg X Y
  rw [nodeReflectedX_scale D d e hkl hl hm h2 a c hc hd hxu i L hi hL,
    nodeReflectedY_scale D d e hkl hl hm z h2 a c hc hd hxu i L hi hL]
  exact (WeierstrassCurve.Projective.equation_some ..).mpr
    (ownSumDepth_original_equation D.uniformizer_ne_zero d e hkl a c i L hi hL)

/-- The actual algebra map into the available reflected-depth chart. -/
def nodeReflectedOutput : Coordinate W (π ^ (m - k - l)) z.b3 z.b4 z.b6 →ₐ[R] S :=
  evaluation W (π ^ (m - k - l)) z.b3 z.b4 z.b6 X Y
    (nodeReflected_equation D d e hkl hl hm z h2 a c hc hd hxu i L hi hL)

local notation "out" => nodeReflectedOutput D d e hkl hl hm z h2 a c hc hd hxu i L hi hL

/-- The target abscissa is exactly the constructed quotient. -/
@[simp] theorem nodeReflectedOutput_x : out (x W (π ^ (m - k - l)) z.b3 z.b4 z.b6) = X :=
  evaluation_x ..

/-- The target ordinate is exactly the constructed quotient. -/
@[simp] theorem nodeReflectedOutput_y : out (y W (π ^ (m - k - l)) z.b3 z.b4 z.b6) = Y :=
  evaluation_y ..

open AlgebraicGeometry CategoryTheory

/-- The same output as a morphism to the actual divided chart. -/
def nodeReflectedLift : Spec (.of S) ⟶ chart z :=
  Spec.map (CommRingCat.ofHom (out).toRingHom)

/-- The constructed output preserves the original coefficient point. -/
@[reassoc] theorem nodeReflectedLift_structure :
    nodeReflectedLift D d e hkl hl hm z h2 a c hc hd hxu i L hi hL ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap R (Coordinate W (π ^ (m - k - l)) z.b3 z.b4 z.b6))) =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) :=
  WeierstrassIntegralChart.specAlgHom_structure _

end FLT.Mazur.WeierstrassDividedDepth
