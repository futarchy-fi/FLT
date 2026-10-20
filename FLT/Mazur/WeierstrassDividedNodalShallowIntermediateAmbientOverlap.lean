/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalIntermediateShallowOverlap
public import FLT.Mazur.WeierstrassDividedNodalIntermediateAmbientAddition
public import FLT.Mazur.WeierstrassDividedNodalShallowAmbientAddition
public import FLT.Mazur.OpenImmersionImageUnionGluedOverlap

/-!
# Compare the entire shallow and intermediate ambient extensions

The literal four pairwise intersections cover the full overlap. The new
cross-depth comparison handles the shallow/intermediate chart intersection.
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
  {W : WeierstrassCurve R} {π : R} {n k m r : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 3 * k ≤ m) (hrk : r ≤ k) (hrm : r ≤ m - 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hr : k + r ≤ n)
  (d : Data W π k)
  (j : ℕ) (hj : j ≤ n) (hkj : k ≤ j) (hrj : k + r ≤ j)
local notation "a" => dividedPairLeft W (π ^ k) d.b3 d.b4 d.b6
local notation "c" => dividedPairRight W (π ^ k) d.b3 d.b4 d.b6
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "O" => nodalIntermediateAdditionOpen D hdepth hrk hrm data hr d a c
local notation "P" => suppliedDividedSmoothInputOpen d a c

local notation "V" => nodalIntermediateSmoothSourceOpen D hdepth hrk hrm data hr d a c
local notation "pair" => nodalIntermediateCommonInput D hdepth hrk hrm data hr d a c j hj hkj
local notation "Old" => finiteResolvedReciprocalExtendedOpen hπ data j hj
local notation "i" => finiteResolvedReciprocalExtendedInput hπ data j hj

variable {l : ℕ} (hs : 2 * l ≤ m) (hsm : m ≤ 3 * l)
  (hsn : m - 2 * l ≤ n) (d' : Data W π l)
  (hlj : l ≤ j) (hsj : m - 2 * l ≤ j)
local notation "a'" => dividedPairLeft W (π ^ l) d'.b3 d'.b4 d'.b6
local notation "c'" => dividedPairRight W (π ^ l) d'.b3 d'.b4 d'.b6
local notation "left" => nodalShallowAmbientInput D hs hsm data hsn d' j hj hlj
local notation "right" => nodalIntermediateAmbientInput D hdepth hrk hrm data hr d j hj hkj
local notation "L" => nodalShallowAmbientOpen D hs hsm data hsn d' j hj hlj
local notation "N" => nodalIntermediateAmbientOpen D hdepth hrk hrm data hr d j hj hkj
local notation "fl" => nodalShallowAmbientAddition D hs hsm data hsn d' j hj hlj hsj
local notation "fr" => nodalIntermediateAmbientAddition D hdepth hrk hrm data hr d j hj hkj hrj

local notation "ol" => nodalShallowAmbientLocal D hs hsm data hsn d' j hj hsj
local notation "orr" => nodalIntermediateAmbientLocal D hdepth hrk hrm data hr d j hj hrj

/-- The old/intermediate literal intersection has its constructed comparison. -/
theorem nodalShallowIntermediateAmbient_oldIntermediate :
    pullback.fst (left false) (right true) ≫ ol false =
      pullback.snd (left false) (right true) ≫ orr true :=
  nodalIntermediateCommonOutput_reciprocalExtendedOverlap
    D hdepth hrk hrm data hr d a c j hj hkj hrj _ _ pullback.condition

/-- The shallow/old literal intersection has its constructed comparison. -/
theorem nodalShallowIntermediateAmbient_shallowOld :
    pullback.fst (left true) (right false) ≫ ol true =
      pullback.snd (left true) (right false) ≫ orr false :=
  (nodalShallowCommonOutput_reciprocalExtendedOverlap
    D hs hsm data hsn d' a' c' j hj hlj hsj _ _ pullback.condition.symm).symm

/-- The new/new literal intersection uses the full cross-depth comparison. -/
theorem nodalShallowIntermediateAmbient_newIntersection :
    pullback.fst (left true) (right true) ≫ ol true =
      pullback.snd (left true) (right true) ≫ orr true :=
  nodalIntermediateCommonOutput_shallowOverlap D hdepth hrk hrm data hr d a c
    j hj hkj hrj hs hsm hsn d' a' c' hlj hsj _ _ pullback.condition

/-- The common old chart agrees with itself. -/
theorem nodalShallowIntermediateAmbient_oldOld :
    pullback.fst (left false) (right false) ≫ ol false =
      pullback.snd (left false) (right false) ≫ orr false := by
  exact congrArg (· ≫ finiteResolvedReciprocalExtendedPartialAddition hπ data j hj)
    ((cancel_mono (Old).ι).mp pullback.condition)

/-- All four literal chart intersections have equal constructed outputs. -/
theorem nodalShallowIntermediateAmbient_local (b b' : Bool) :
    pullback.fst (left b) (right b') ≫ ol b =
      pullback.snd (left b) (right b') ≫ orr b' := by
  cases b <;> cases b'
  · exact nodalShallowIntermediateAmbient_oldOld
      D hdepth hrk hrm data hr d j hj hkj hrj hs hsm hsn d' hlj hsj
  · exact nodalShallowIntermediateAmbient_oldIntermediate
      D hdepth hrk hrm data hr d j hj hkj hrj hs hsm hsn d' hlj hsj
  · exact nodalShallowIntermediateAmbient_shallowOld
      D hdepth hrk hrm data hr d j hj hkj hrj hs hsm hsn d' hlj hsj
  · exact nodalShallowIntermediateAmbient_newIntersection
      D hdepth hrk hrm data hr d j hj hkj hrj hs hsm hsn d' hlj hsj

/-- The two entire ambient extensions agree on their actual full fiber product. -/
theorem nodalShallowIntermediateAmbient_pullback :
    pullback.fst (L).ι (N).ι ≫ fl = pullback.snd (L).ι (N).ι ≫ fr :=
  openImageUnionGlue_pullback_eq left right ol orr _ _
    (nodalShallowIntermediateAmbient_local D hdepth hrk hrm data hr d j hj hkj hrj
      hs hsm hsn d' hlj hsj)

/-- Every common-source comparison follows from the full fiber-product equality. -/
theorem nodalShallowIntermediateAmbient_overlap {X : Scheme}
    (p : X ⟶ (L).toScheme) (q : X ⟶ (N).toScheme)
    (hpq : p ≫ (L).ι = q ≫ (N).ι) : p ≫ fl = q ≫ fr := by
  have h := congrArg (pullback.lift p q hpq ≫ ·)
    (nodalShallowIntermediateAmbient_pullback D hdepth hrk hrm data hr d j hj hkj hrj
      hs hsm hsn d' hlj hsj)
  simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using h

end FLT.Mazur.WeierstrassDividedDepth
