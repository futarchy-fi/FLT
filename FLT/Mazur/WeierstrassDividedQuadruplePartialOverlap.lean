/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedQuadrupleLeftOverlap
public import FLT.Mazur.WeierstrassDividedQuadrupleRightOverlap
public import FLT.Mazur.WeierstrassDividedResolvedPartialAddition

/-!
# Quadruple-depth compatibility on a whole previously glued domain

Pull back the existing constituent cover and apply the actual overlap
comparisons on each member. This preserves the full quadruple-depth common source.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure rootShearCurve
  nodalSecondShear nodalSecondQuotient
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (D : SplitNodeDepth W π (4 * k)) (d : Data W π k)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "data" => splitNodeDoubledFamily D
local notation "j" => k + k
local notation "hj" => (le_rfl : k + k ≤ k + k)
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "O" => nodalQuadrupleAdditionOpen D d a c
local notation "P" => suppliedDividedSmoothInputOpen d a c

local notation "V" => quadrupleSmoothSourceOpen D d a c
local notation "pair" => quadrupleCommonInput D d a c
local notation "Old" => finiteResolvedOriginalFactorOpen hπ data j hj
local notation "i" => finiteResolvedInput hπ data j hj

/-- Both originally smooth input orders agree with the entire quadruple-depth law. -/
theorem quadrupleCommonOutput_orderOverlap {X : Scheme} (b : Bool)
    (p : X ⟶ pullback (integralSmoothStructure W) t)
    (q : X ⟶ (V).toScheme) [Flat q] (hpq : p ≫ i b = q ≫ pair) :
    p ≫ finiteGlobalSmoothAction hπ data j hj =
      q ≫ quadrupleCommonOutput D d a c := by
  cases b
  · exact quadrupleCommonOutput_leftOverlap D d a c p q hpq
  · exact quadrupleCommonOutput_rightOverlap D d a c p q hpq

/-- The originally smooth partial law agrees on every flat quadruple-depth overlap. -/
theorem quadrupleCommonOutput_partialOverlap {X : Scheme}
    (p : X ⟶ (Old).toScheme) (q : X ⟶ (V).toScheme) [Flat q]
    (hpq : p ≫ (Old).ι = q ≫ pair) :
    p ≫ finiteResolvedPartialAddition hπ data j hj =
      q ≫ quadrupleCommonOutput D d a c := by
  apply Scheme.Cover.hom_ext ((openImageUnionCover i).pullback₁ p)
  intro b
  change Bool at b
  let f := pullback.fst p (openImageUnionMap i b)
  let g := pullback.snd p (openImageUnionMap i b)
  have hp : f ≫ p = g ≫ openImageUnionMap i b := pullback.condition
  have he : g ≫ i b = (f ≫ q) ≫ pair := by
    symm
    rw [Category.assoc, ← hpq, ← Category.assoc, hp, Category.assoc]
    exact congrArg (g ≫ ·) (openImageUnionMap_fac i b)
  have h := quadrupleCommonOutput_orderOverlap D d a c b g (f ≫ q) he
  rw [← finiteResolvedPartialAddition_chart hπ data j hj b,
    ← Category.assoc, ← hp, Category.assoc] at h
  exact h

end FLT.Mazur.WeierstrassDividedDepth
