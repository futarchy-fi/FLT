/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDeepCommonModel
public import FLT.Mazur.WeierstrassDividedNodalInputSmoothVertical

/-!
# Deep-node addition covers the full relatively smooth nodal input domain

On the deep nodal fiber with m > 4*k, the two vertical nonvanishing conditions follow
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
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ}
  (D : SplitNodeDepth W π m)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hkk : k + k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "O" => nodalDeepAdditionOpen D data hkk d a c
local notation "P" => suppliedDividedSmoothInputOpen d a c
local notation "dx" => a (x W (π ^ k) (d).b3 (d).b4 (d).b6) -
  c (x W (π ^ k) (d).b3 (d).b4 (d).b6)
local notation "E" => dividedTangentDenominator W (π ^ k) (d).b3 (d).b4 (d).b6 a c

/-- Relative smoothness alone gives a deep-node output in either original formula open. -/
theorem nodalDeepAdditionOpen_source_relativeSmooth
    (hpos : 0 < k) (hm : 4 * k < m) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal) (hs : p ∈ P)
    (hformula : dx ∉ p.asIdeal ∨ E ∉ p.asIdeal) : p ∈ O := by
  have hlo : 2 * k < m := by omega
  apply nodalDeepAdditionOpen_source_cover D data hkk d a c hpos hm p hp _ _ hformula
  · exact nodalDividedInput_smooth_vertical D d a hpos hlo p hp hs.1
  · exact nodalDividedInput_smooth_vertical D d c hpos hlo p hp hs.2

/-- The constructed common-model source covers every relatively smooth nodal formula input. -/
theorem deepSmoothSourceOpen_covers
    (hpos : 0 < k) (hm : 4 * k < m) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal) (hs : p ∈ P)
    (hformula : dx ∉ p.asIdeal ∨ E ∉ p.asIdeal) :
    p ∈ deepSmoothSourceOpen D data hkk d a c :=
  ⟨nodalDeepAdditionOpen_source_relativeSmooth D data hkk d a c
    hpos hm p hp hs hformula, hs⟩

end FLT.Mazur.WeierstrassDividedDepth
