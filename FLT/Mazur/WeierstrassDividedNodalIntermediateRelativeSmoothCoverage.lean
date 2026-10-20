/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalIntermediateCommonModel
public import FLT.Mazur.WeierstrassDividedNodalInputSmoothVertical

/-!
# Intermediate addition covers the full relatively smooth nodal input domain

On the strict nodal fiber, the two vertical nonvanishing conditions follow
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
  {W : WeierstrassCurve R} {π : R} {n k m r : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 3 * k ≤ m) (hrk : r ≤ k) (hrm : r ≤ m - 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hr : k + r ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "O" => nodalIntermediateAdditionOpen D hdepth hrk hrm data hr d a c
local notation "P" => suppliedDividedSmoothInputOpen d a c
local notation "dx" => a (x W (π ^ k) d.b3 d.b4 d.b6) -
  c (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "E" => dividedTangentDenominator W (π ^ k) d.b3 d.b4 d.b6 a c

/-- Relative smoothness alone gives an intermediate output in either original formula open. -/
theorem nodalIntermediateAdditionOpen_source_relativeSmooth
    (hk : 0 < k) (hhi : m < 4 * k) (heq : r = m - 3 * k) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal) (hs : p ∈ P)
    (hformula : dx ∉ p.asIdeal ∨ E ∉ p.asIdeal) : p ∈ O := by
  apply nodalIntermediateAdditionOpen_source_cover D hdepth hrk hrm data hr d a c
    hk hhi heq p hp _ _ hformula
  · exact nodalDividedInput_smooth_vertical D d a hk (by omega) p hp hs.1
  · exact nodalDividedInput_smooth_vertical D d c hk (by omega) p hp hs.2

/-- The constructed common-model source covers every relatively smooth nodal formula input. -/
theorem nodalIntermediateSmoothSourceOpen_covers
    (hk : 0 < k) (hhi : m < 4 * k) (heq : r = m - 3 * k) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal) (hs : p ∈ P)
    (hformula : dx ∉ p.asIdeal ∨ E ∉ p.asIdeal) :
    p ∈ nodalIntermediateSmoothSourceOpen D hdepth hrk hrm data hr d a c :=
  ⟨nodalIntermediateAdditionOpen_source_relativeSmooth D hdepth hrk hrm data hr d a c
    hk hhi heq p hp hs hformula, hs⟩

end FLT.Mazur.WeierstrassDividedDepth
