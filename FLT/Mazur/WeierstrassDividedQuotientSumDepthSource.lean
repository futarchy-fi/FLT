/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSumDepthSourceOutput
public import FLT.Mazur.WeierstrassDividedQuotientSumDepthOutput

/-!
# The quotient sum-depth output on the original principal open

The input coefficient quotients replace doubled-depth data. All unit
conditions, the secant inverse, and its slope come from the
principal-open source. The output chart map needs only coefficient data
and normalization, with no assumed output coordinates or smoothness.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {W : WeierstrassCurve R} {π : R} {k l : ℕ} (d : Data W π k) (e : Data W π l)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "B" => SumDepthSourceRing d e a c
local notation "j" => IsScalarTower.toAlgHom R S B
local notation "a'" => (j).comp a
local notation "c'" => (j).comp c

variable [IsDomain R] [Module.Flat R S] (hπ : π ≠ 0) (hkl : k ≤ l)
  (dd : BranchQuotientData d) (ee : BranchQuotientData e) (z : Data W π (k + l))
  (h2 : W.a₂ = 0)
local notation "hc" => sumDepthSource_leftUnit d e a c
local notation "hd" => sumDepthSource_rightUnit d e a c
local notation "hxu" => sumDepthSource_abscissaUnit d e a c
local notation "i" => sumDepthSourceInverse d e a c hπ hkl
local notation "L" => sumDepthSourceSlope d e a c hπ hkl
local notation "hi" => sumDepthSourceInverse_relation d e a c hπ hkl
local notation "hL" => sumDepthSourceSlope_relation d e a c hπ hkl

/-- The complete coordinate map on the constructed principal-open source. -/
def quotientSumDepthSourceOutput : Coordinate W (π ^ (k + l)) z.b3 z.b4 z.b6 →ₐ[R] B :=
  quotientSumDepthOutput hπ d e hkl dd ee z h2 a' c' hc hd hxu i L hi hL

local notation "out" => quotientSumDepthSourceOutput d e a c hπ hkl dd ee z h2

/-- The output abscissa is the explicit constructed sum-depth quotient. -/
@[simp] theorem quotientSumDepthSourceOutput_x :
    out (x W (π ^ (k + l)) z.b3 z.b4 z.b6) =
      quotientSumDepthX d e dd ee z a' c' hc hd hxu i :=
  quotientSumDepthOutput_x hπ d e hkl dd ee z h2 a' c' hc hd hxu i L hi hL

/-- The output ordinate uses exactly the same source and scale. -/
@[simp] theorem quotientSumDepthSourceOutput_y :
    out (y W (π ^ (k + l)) z.b3 z.b4 z.b6) =
      quotientSumDepthY d e dd ee z a' c' hc hd hxu i L :=
  quotientSumDepthOutput_y hπ d e hkl dd ee z h2 a' c' hc hd hxu i L hi hL

/-- The actual source open maps to the sum-depth divided chart. -/
def quotientSumDepthSourceLift : Spec (.of B) ⟶ chart z :=
  Spec.map (CommRingCat.ofHom (out).toRingHom)

/-- The new chart output lies over the actual input coefficient point. -/
@[reassoc] theorem quotientSumDepthSourceLift_structure :
    quotientSumDepthSourceLift d e a c hπ hkl dd ee z h2 ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (Coordinate W (π ^ (k + l)) z.b3 z.b4 z.b6))) =
        Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
  WeierstrassIntegralChart.specAlgHom_structure _

end FLT.Mazur.WeierstrassDividedDepth
