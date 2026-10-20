/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleCommonModel
public import FLT.Mazur.WeierstrassDividedNodalInputSmoothVertical

/-!
# Exact-triple addition covers the full relatively smooth nodal input domain

On the positive-depth exact-triple nodal fiber, the two vertical nonvanishing conditions follow
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
  {W : WeierstrassCurve R} {π : R} {start n k : ℕ}
  (D : SplitNodeDepth W π (3 * (start + k)))
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  (a c : Coordinate W (π ^ (start + k))
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b3 (data ⟨k, Nat.lt_succ_of_le hk⟩).b4
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b6 →ₐ[R] S)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
local notation "O" => tripleAdditionOpen D data hk a c
local notation "P" => suppliedDividedSmoothInputOpen d a c
local notation "dx" => a (x W (π ^ (start + k)) (d).b3 (d).b4 (d).b6) -
  c (x W (π ^ (start + k)) (d).b3 (d).b4 (d).b6)
local notation "E" => dividedTangentDenominator W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 a c

/-- Relative smoothness alone gives an exact-triple output in either original formula open. -/
theorem tripleAdditionOpen_source_relativeSmooth
    (hpos : 0 < start + k) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal) (hs : p ∈ P)
    (hformula : dx ∉ p.asIdeal ∨ E ∉ p.asIdeal) : p ∈ O := by
  have hlo : 2 * (start + k) < 3 * (start + k) := by omega
  apply tripleAdditionOpen_source_cover D data hk a c p hp _ _ hformula
  · exact nodalDividedInput_smooth_vertical D d a hpos hlo p hp hs.1
  · exact nodalDividedInput_smooth_vertical D d c hpos hlo p hp hs.2

/-- The constructed common-model source covers every relatively smooth nodal formula input. -/
theorem tripleSmoothSourceOpen_covers
    (hpos : 0 < start + k) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal) (hs : p ∈ P)
    (hformula : dx ∉ p.asIdeal ∨ E ∉ p.asIdeal) :
    p ∈ tripleSmoothSourceOpen D data hk a c :=
  ⟨tripleAdditionOpen_source_relativeSmooth D data hk a c
    hpos p hp hs hformula, hs⟩

end FLT.Mazur.WeierstrassDividedDepth
