/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCommonSumOutput
public import FLT.Mazur.WeierstrassDividedQuotientSumDepthOutput

/-!
# Common-scale and own-scale sum outputs agree

Whenever both coefficient presentations exist, regularity of the original
sum-depth scale identifies the entire divided coordinate map. This is a
comparison on the full supplied flat source, with no generic-point restriction.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [Module.Flat R S] {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k l : ℕ}
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (dd : BranchQuotientData d) (ee : CommonBranchData e k) (z : Data W π (k + l))
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
local notation "q" => quotientBranchOrdinate d dd a hc
local notation "r" => commonBranchOrdinate e ee c hd
local notation "b" => sumDepthIntercept 1 x₁ x₂ q r i

variable (hi : i * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) = 1)
  (hL : L * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) =
      a (y W (π ^ k) d.b3 d.b4 d.b6) -
        algebraMap R S (π ^ (l - k)) * c (y W (π ^ l) e.b3 e.b4 e.b6))

variable (ee' : BranchQuotientData e)
local notation "new" => commonSumDepthOutput hπ d e hkl dd ee z h2 a c hc hd hxu i L hi hL
local notation "old" => quotientSumDepthOutput hπ d e hkl dd ee' z h2 a c hc hd hxu i L hi hL

include hπ hkl h2 hi hL in
/-- Both coefficient constructions give the same abscissa on the entire flat source. -/
theorem commonSumDepthX_eq_quotient :
    commonSumDepthX d e dd ee z a c hc hd hxu i =
      quotientSumDepthX d e dd ee' z a c hc hd hxu i := by
  apply (ownSumDepth_regular hπ (k := k) (l := l) (S := S)).left
  exact (commonSumDepthX_scale hπ d e hkl dd ee z h2 a c hc hd hxu i L hi hL).trans
    (quotientSumDepthX_scale hπ d e hkl dd ee' z h2 a c hc hd hxu i L hi hL).symm

include hπ hkl h2 hi hL in
/-- The ordinate agrees without discarding any closed-fiber information. -/
theorem commonSumDepthY_eq_quotient :
    commonSumDepthY d e dd ee z a c hc hd hxu i L =
      quotientSumDepthY d e dd ee' z a c hc hd hxu i L := by
  apply (ownSumDepth_regular hπ (k := k) (l := l) (S := S)).left
  exact (commonSumDepthY_scale hπ d e hkl dd ee z h2 a c hc hd hxu i L hi hL).trans
    (quotientSumDepthY_scale hπ d e hkl dd ee' z h2 a c hc hd hxu i L hi hL).symm

/-- Equality holds for every function of the divided output coordinate algebra. -/
theorem commonSumDepthOutput_eq_quotient : new = old := by
  apply hom_ext
  · simp only [commonSumDepthOutput_x, quotientSumDepthOutput_x]
    exact commonSumDepthX_eq_quotient hπ d e hkl dd ee z h2 a c hc hd hxu i L hi hL ee'
  · simp only [commonSumDepthOutput_y, quotientSumDepthOutput_y]
    exact commonSumDepthY_eq_quotient hπ d e hkl dd ee z h2 a c hc hd hxu i L hi hL ee'

end FLT.Mazur.WeierstrassDividedDepth
