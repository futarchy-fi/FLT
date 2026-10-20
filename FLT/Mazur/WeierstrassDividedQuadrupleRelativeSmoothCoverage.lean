/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedQuadrupleCommonModel
public import FLT.Mazur.WeierstrassDividedNodalInputSmoothVertical

/-!
# Quadruple-depth addition covers the full relatively smooth nodal input domain

On the quadruple-depth nodal fiber, the two vertical nonvanishing conditions follow
from relative smoothness of the actual inputs. Both original formula opens
therefore have constructed common-stage outputs without additional derivative
hypotheses. Coverage of the complementary reciprocal domain remains separate.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (D : SplitNodeDepth W π (4 * k)) (d : Data W π k)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "O" => nodalQuadrupleAdditionOpen D d a c
local notation "P" => suppliedDividedSmoothInputOpen d a c
local notation "dx" => a (x W (π ^ k) (d).b3 (d).b4 (d).b6) -
  c (x W (π ^ k) (d).b3 (d).b4 (d).b6)
local notation "E" => dividedTangentDenominator W (π ^ k) (d).b3 (d).b4 (d).b6 a c

/-- Relative smoothness alone gives a quadruple-depth output in either original formula open. -/
theorem nodalQuadrupleAdditionOpen_source_relativeSmooth
    (hpos : 0 < k) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal) (hs : p ∈ P)
    (hformula : dx ∉ p.asIdeal ∨ E ∉ p.asIdeal) : p ∈ O := by
  have hlo : 2 * k < 4 * k := by omega
  apply nodalQuadrupleAdditionOpen_source_cover D d a c hpos p hp _ _ hformula
  · exact nodalDividedInput_smooth_vertical D d a hpos hlo p hp hs.1
  · exact nodalDividedInput_smooth_vertical D d c hpos hlo p hp hs.2

/-- The constructed common-model source covers every relatively smooth nodal formula input. -/
theorem quadrupleSmoothSourceOpen_covers
    (hpos : 0 < k) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal) (hs : p ∈ P)
    (hformula : dx ∉ p.asIdeal ∨ E ∉ p.asIdeal) :
    p ∈ quadrupleSmoothSourceOpen D d a c :=
  ⟨nodalQuadrupleAdditionOpen_source_relativeSmooth D d a c
    hpos p hp hs hformula, hs⟩

end FLT.Mazur.WeierstrassDividedDepth
