/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleShallowOverlap
public import FLT.Mazur.WeierstrassDividedTripleAmbientAddition
public import FLT.Mazur.WeierstrassDividedNodalShallowAmbientAddition
public import FLT.Mazur.OpenImmersionImageUnionGluedOverlap

/-!
# Compare the entire shallow and exact-triple ambient extensions

The literal four pairwise intersections cover the full overlap. The new
cross-depth comparison handles the shallow/exact-triple chart intersection.
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
variable {R : Type} [CommRing R] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} {n k : ℕ}
  (D : SplitNodeDepth W π (3 * (0 + k)))
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hk : k ≤ n)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
variable (j : ℕ) (hj : j ≤ n) (hkj : k ≤ j)
local notation "a" => dividedPairLeft W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6
local notation "c" => dividedPairRight W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6
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

variable {l : ℕ} (hs : 2 * l ≤ 3 * (0 + k)) (hsm : 3 * (0 + k) ≤ 3 * l)
  (hsn : 3 * (0 + k) - 2 * l ≤ n) (d' : Data W π l)
  (hlj : l ≤ j) (hsj : 3 * (0 + k) - 2 * l ≤ j)
local notation "a'" => dividedPairLeft W (π ^ l) d'.b3 d'.b4 d'.b6
local notation "c'" => dividedPairRight W (π ^ l) d'.b3 d'.b4 d'.b6
local notation "left" => nodalShallowAmbientInput D hs hsm data hsn d' j hj hlj
local notation "right" => tripleAmbientInput D data hk j hj hkj
local notation "L" => nodalShallowAmbientOpen D hs hsm data hsn d' j hj hlj
local notation "N" => tripleAmbientOpen D data hk j hj hkj
local notation "fl" => nodalShallowAmbientAddition D hs hsm data hsn d' j hj hlj hsj
local notation "fr" => tripleAmbientAddition D data hk j hj hkj

local notation "ol" => nodalShallowAmbientLocal D hs hsm data hsn d' j hj hsj
local notation "orr" => tripleAmbientLocal D data hk j hj hkj

/-- The old/exact-triple literal intersection has its constructed comparison. -/
theorem shallowTripleAmbient_oldTriple :
    pullback.fst (left false) (right true) ≫ ol false =
      pullback.snd (left false) (right true) ≫ orr true :=
  tripleCommonOutput_reciprocalExtendedOverlap
    D data hk a c j hj hkj _ _ pullback.condition

/-- The shallow/old literal intersection has its constructed comparison. -/
theorem shallowTripleAmbient_shallowOld :
    pullback.fst (left true) (right false) ≫ ol true =
      pullback.snd (left true) (right false) ≫ orr false :=
  (nodalShallowCommonOutput_reciprocalExtendedOverlap
    D hs hsm data hsn d' a' c' j hj hlj hsj _ _ pullback.condition.symm).symm

/-- The new/new literal intersection uses the full cross-depth comparison. -/
theorem shallowTripleAmbient_newIntersection :
    pullback.fst (left true) (right true) ≫ ol true =
      pullback.snd (left true) (right true) ≫ orr true :=
  tripleCommonOutput_shallowOverlap D data hk a c
    j hj hkj hs hsm hsn d' a' c' hlj hsj _ _ pullback.condition

/-- The common old chart agrees with itself. -/
theorem shallowTripleAmbient_oldOld :
    pullback.fst (left false) (right false) ≫ ol false =
      pullback.snd (left false) (right false) ≫ orr false := by
  exact congrArg (· ≫ finiteResolvedReciprocalExtendedPartialAddition hπ data j hj)
    ((cancel_mono (Old).ι).mp pullback.condition)

/-- All four literal chart intersections have equal constructed outputs. -/
theorem shallowTripleAmbient_local (b b' : Bool) :
    pullback.fst (left b) (right b') ≫ ol b =
      pullback.snd (left b) (right b') ≫ orr b' := by
  cases b <;> cases b'
  · exact shallowTripleAmbient_oldOld
      D data hk j hj hkj hs hsm hsn d' hlj hsj
  · exact shallowTripleAmbient_oldTriple
      D data hk j hj hkj hs hsm hsn d' hlj hsj
  · exact shallowTripleAmbient_shallowOld
      D data hk j hj hkj hs hsm hsn d' hlj hsj
  · exact shallowTripleAmbient_newIntersection
      D data hk j hj hkj hs hsm hsn d' hlj hsj

/-- The two entire ambient extensions agree on their actual full fiber product. -/
theorem shallowTripleAmbient_pullback :
    pullback.fst (L).ι (N).ι ≫ fl = pullback.snd (L).ι (N).ι ≫ fr :=
  openImageUnionGlue_pullback_eq left right ol orr _ _
    (shallowTripleAmbient_local D data hk j hj hkj
      hs hsm hsn d' hlj hsj)

/-- Every common-source comparison follows from the full fiber-product equality. -/
theorem shallowTripleAmbient_overlap {X : Scheme}
    (p : X ⟶ (L).toScheme) (q : X ⟶ (N).toScheme)
    (hpq : p ≫ (L).ι = q ≫ (N).ι) : p ≫ fl = q ≫ fr := by
  have h := congrArg (pullback.lift p q hpq ≫ ·)
    (shallowTripleAmbient_pullback D data hk j hj hkj
      hs hsm hsn d' hlj hsj)
  simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using h

end FLT.Mazur.WeierstrassDividedDepth
