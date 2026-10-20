/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleExtendedOverlap
public import FLT.Mazur.WeierstrassDividedTripleTangentOverlap
public import FLT.Mazur.WeierstrassDividedTangentExtendedAddition

/-!
# Exact-triple compatibility on a whole previously glued domain

Pull back the existing constituent cover and apply the actual overlap
comparisons on each member. This preserves the full exact-triple common source.
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
  {W : WeierstrassCurve R} {π : R} {start n k : ℕ}
  (D : SplitNodeDepth W π (3 * (start + k)))
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  (a c : Coordinate W (π ^ (start + k))
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b3 (data ⟨k, Nat.lt_succ_of_le hk⟩).b4
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b6 →ₐ[R] S)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
variable (j : ℕ) (hj : j ≤ n) (hkj : k ≤ j)
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "O" => tripleAdditionOpen D data hk a c
local notation "P" => suppliedDividedSmoothInputOpen d a c

local notation "V" => tripleSmoothSourceOpen D data hk a c
local notation "pair" => tripleCommonInput D data hk a c j hj hkj
local notation "Old" => finiteResolvedTangentExtendedOpen hπ data j hj
local notation "i" => finiteResolvedTangentExtendedInput hπ data j hj

/-- The whole tangentextended law agrees on every flat exact-triple-common-source overlap. -/
theorem tripleCommonOutput_tangentExtendedOverlap {X : Scheme}
    (p : X ⟶ (Old).toScheme) (q : X ⟶ (V).toScheme) [Flat q]
    (hpq : p ≫ (Old).ι = q ≫ pair) :
    p ≫ finiteResolvedTangentExtendedPartialAddition hπ data j hj =
      q ≫ tripleCommonOutput D data hk a c j hj hkj := by
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
  cases b
  · have h := tripleCommonOutput_extendedOverlap
      D data hk a c j hj hkj g (f ≫ q) he
    rw [← finiteResolvedTangentExtendedPartialAddition_old hπ data j hj,
      ← Category.assoc, ← hp, Category.assoc] at h
    exact h
  · have h := tripleCommonOutput_tangentOverlap
      D data hk a c j hj hkj g (f ≫ q) he
    rw [← finiteResolvedTangentExtendedPartialAddition_tangent hπ data j hj,
      ← Category.assoc, ← hp, Category.assoc] at h
    exact h

end FLT.Mazur.WeierstrassDividedDepth
