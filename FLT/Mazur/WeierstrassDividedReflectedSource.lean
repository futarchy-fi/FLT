/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSumDepthSourceOutput
public import FLT.Mazur.WeierstrassDividedReflectedBranchOutput

/-!
# Reflected-depth output on the original principal open

All units, the secant inverse, and its slope come from the original source.
The reflected output can exist when the sum-depth chart is unavailable.
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
  {W : WeierstrassCurve R} {π : R} {k l m : ℕ} (d : Data W π k) (e : Data W π l)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "B" => SumDepthSourceRing d e a c
local notation "j" => IsScalarTower.toAlgHom R S B
local notation "a'" => (j).comp a
local notation "c'" => (j).comp c

variable [IsDomain R] [IsLocalRing R] [Module.Flat R S]
  (D : SplitNodeDepth W π m) (hkl : k ≤ l) (hl : 2 * l ≤ m) (hm : m ≤ k + 2 * l)
  (z : Data W π (m - k - l))
  (h2 : W.a₂ = 0)
local notation "hc" => sumDepthSource_leftUnit d e a c
local notation "hd" => sumDepthSource_rightUnit d e a c
local notation "hxu" => sumDepthSource_abscissaUnit d e a c
local notation "i" => sumDepthSourceInverse d e a c D.uniformizer_ne_zero hkl
local notation "L" => sumDepthSourceSlope d e a c D.uniformizer_ne_zero hkl
local notation "hi" => sumDepthSourceInverse_relation d e a c D.uniformizer_ne_zero hkl
local notation "hL" => sumDepthSourceSlope_relation d e a c D.uniformizer_ne_zero hkl

/-- The complete coordinate map on the constructed principal-open source. -/
def reflectedSourceOutput : Coordinate W (π ^ (m - k - l)) z.b3 z.b4 z.b6 →ₐ[R] B :=
  nodeReflectedOutput D d e hkl hl hm z h2 a' c' hc hd hxu i L hi hL

local notation "out" => reflectedSourceOutput d e a c D hkl hl hm z h2

/-- The output abscissa is the explicit constructed reflected-depth quotient. -/
@[simp] theorem reflectedSourceOutput_x :
    out (x W (π ^ (m - k - l)) z.b3 z.b4 z.b6) =
      nodeReflectedX D d e hkl hl a' c' hc hd hxu i :=
  nodeReflectedOutput_x D d e hkl hl hm z h2 a' c' hc hd hxu i L hi hL

/-- The output ordinate uses exactly the same source and scale. -/
@[simp] theorem reflectedSourceOutput_y :
    out (y W (π ^ (m - k - l)) z.b3 z.b4 z.b6) =
      nodeReflectedY D d e hkl hl z a' c' hc hd hxu i L :=
  nodeReflectedOutput_y D d e hkl hl hm z h2 a' c' hc hd hxu i L hi hL

/-- The actual source open maps to the reflected-depth divided chart. -/
def reflectedSourceLift : Spec (.of B) ⟶ chart z :=
  Spec.map (CommRingCat.ofHom (out).toRingHom)

/-- The new chart output lies over the actual input coefficient point. -/
@[reassoc] theorem reflectedSourceLift_structure :
    reflectedSourceLift d e a c D hkl hl hm z h2 ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (Coordinate W (π ^ (m - k - l)) z.b3 z.b4 z.b6))) =
        Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
  WeierstrassIntegralChart.specAlgHom_structure _

end FLT.Mazur.WeierstrassDividedDepth
