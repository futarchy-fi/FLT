/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleReciprocalExtendedOverlap

/-!
# The actual entire exact-triple/reciprocal-extended pullback

The old domain is open in the resolved product. Its pullback gives the flat
refinement required by the comparison, without any extra geometric hypothesis.
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
local notation "Old" => finiteResolvedReciprocalExtendedOpen hπ data j hj
local notation "i" => finiteResolvedReciprocalExtendedInput hπ data j hj

/-- The two constructed laws agree on their actual full fiber-product intersection. -/
theorem tripleCommonOutput_reciprocalExtendedPullback :
    pullback.fst (Old).ι pair ≫ finiteResolvedReciprocalExtendedPartialAddition hπ data j hj =
      pullback.snd (Old).ι pair ≫
        tripleCommonOutput D data hk a c j hj hkj :=
  tripleCommonOutput_reciprocalExtendedOverlap D data hk a c
    j hj hkj _ _ pullback.condition

end FLT.Mazur.WeierstrassDividedDepth
