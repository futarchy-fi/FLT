/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOwnSumDepthCoordinates

/-!
# Actual coordinate maps into the sum-depth chart

The constructed coordinates satisfy the divided equation by regularity of
the sum-depth scale. This gives an algebra map and a scheme-valued output,
with no smoothness or output point supplied as input data.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [Module.Flat R S] {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k l : ℕ}
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (dd : Data W π (k + k)) (ee : Data W π (l + l)) (z : Data W π (k + l))
  (h2 : W.a₂ = 0)
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
local notation "q" => ownBranchOrdinate d dd a hc
local notation "r" => ownBranchOrdinate e ee c hd
local notation "b" => sumDepthIntercept t x₁ x₂ q r i

variable (hi : i * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) = 1)
  (hL : L * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) =
      a (y W (π ^ k) d.b3 d.b4 d.b6) -
        algebraMap R S (π ^ (l - k)) * c (y W (π ^ l) e.b3 e.b4 e.b6))

local notation "X" => ownSumDepthX d e dd ee z a c hc hd hxu i
local notation "Y" => ownSumDepthY d e dd ee z a c hc hd hxu i L

include hπ in
/-- Flatness keeps the sum-depth scale regular. -/
theorem ownSumDepth_regular : IsRegular (algebraMap R S (π ^ (k + l))) :=
  WeierstrassIntegralChart.flatRingHom_isRegular _
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
    (isRegular_iff_ne_zero.mpr (pow_ne_zero _ hπ))

omit [Module.Flat R S] in
include hπ hkl hi hL in
/-- The original secant equation holds for the constructed chord. -/
theorem ownSumDepth_original_equation :
    (W').toAffine.Equation ((W').toAffine.addX (s * x₁) (s * (t * x₂)) L)
      ((W').toAffine.addY (s * x₁) (s * (t * x₂)) (s * y₁) L) := by
  have he := equation_map W (π ^ k) d.b3 d.b4 d.b6
    (unequalDepthRight hπ d e hkl c)
  simp only [unequalDepthRight_x, unequalDepthRight_y] at he
  apply divided_secant_add_equation W' s (algebraMap R S d.b3)
    (algebraMap R S d.b4) (algebraMap R S d.b6)
  · simpa only [WeierstrassCurve.map_a₃, map_mul] using congrArg (algebraMap R S) d.factor3
  · simpa only [WeierstrassCurve.map_a₄, map_mul] using congrArg (algebraMap R S) d.factor4
  · simpa only [WeierstrassCurve.map_a₆, map_mul, map_pow] using
      congrArg (algebraMap R S) d.factor6
  · exact equation_map W (π ^ k) d.b3 d.b4 d.b6 a
  · exact he
  · exact isUnit_iff_exists_inv.mpr ⟨i, by rwa [mul_comm]⟩
  · exact hL

include hπ hkl h2 hi hL in
/-- The two computed sum-depth coordinates satisfy the entire target equation. -/
theorem ownSumDepth_equation :
    Y ^ 2 + (algebraMap R S W.a₁ * X + algebraMap R S z.b3) * Y =
      algebraMap R S (π ^ (k + l)) * X ^ 3 + algebraMap R S W.a₂ * X ^ 2 +
        algebraMap R S z.b4 * X + algebraMap R S z.b6 := by
  apply equation_of_scaled W (π ^ (k + l)) z.b3 z.b4 z.b6
    z.factor3 z.factor4 z.factor6 (ownSumDepth_regular hπ) X Y
  rw [ownSumDepthX_scale hπ d e hkl dd ee z h2 a c hc hd hxu i L hi hL,
    ownSumDepthY_scale hπ d e hkl dd ee z h2 a c hc hd hxu i L hi hL]
  exact (WeierstrassCurve.Projective.equation_some ..).mpr
    (ownSumDepth_original_equation hπ d e hkl a c i L hi hL)

/-- The actual algebra map into the available sum-depth chart. -/
def ownSumDepthOutput : Coordinate W (π ^ (k + l)) z.b3 z.b4 z.b6 →ₐ[R] S :=
  evaluation W (π ^ (k + l)) z.b3 z.b4 z.b6 X Y
    (ownSumDepth_equation hπ d e hkl dd ee z h2 a c hc hd hxu i L hi hL)

local notation "out" => ownSumDepthOutput hπ d e hkl dd ee z h2 a c hc hd hxu i L hi hL

/-- The target abscissa is exactly the constructed quotient. -/
@[simp] theorem ownSumDepthOutput_x : out (x W (π ^ (k + l)) z.b3 z.b4 z.b6) = X :=
  evaluation_x ..

/-- The target ordinate is exactly the constructed quotient. -/
@[simp] theorem ownSumDepthOutput_y : out (y W (π ^ (k + l)) z.b3 z.b4 z.b6) = Y :=
  evaluation_y ..

open AlgebraicGeometry CategoryTheory

/-- The same output as a morphism to the actual divided chart. -/
def ownSumDepthLift : Spec (.of S) ⟶ chart z :=
  Spec.map (CommRingCat.ofHom (out).toRingHom)

/-- The constructed output preserves the original coefficient point. -/
@[reassoc] theorem ownSumDepthLift_structure :
    ownSumDepthLift hπ d e hkl dd ee z h2 a c hc hd hxu i L hi hL ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap R (Coordinate W (π ^ (k + l)) z.b3 z.b4 z.b6))) =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) :=
  WeierstrassIntegralChart.specAlgHom_structure _

end FLT.Mazur.WeierstrassDividedDepth
