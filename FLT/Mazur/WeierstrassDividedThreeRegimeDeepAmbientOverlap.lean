/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThreeRegimeAmbientAddition
public import FLT.Mazur.WeierstrassDividedShallowDeepAmbientOverlap
public import FLT.Mazur.WeierstrassDividedTripleDeepAmbientOverlap
public import FLT.Mazur.WeierstrassDividedIntermediateDeepAmbientOverlap
public import FLT.Mazur.OpenImmersionImageUnionSingleOverlap

/-!
# Compare the whole three-regime ambient law with the deep extension

Each existing ambient chart compares with the entire deep ambient extension.
Their actual cover descends the comparisons to the whole three-regime union.
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
  {W : WeierstrassCurve R} {π : R} {n k r q : ℕ}
  (D : SplitNodeDepth W π (3 * (0 + q)))
  (hdepth : 3 * k ≤ 3 * (0 + q)) (hrk : r ≤ k) (hrm : r ≤ 3 * (0 + q) - 3 * k)
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

variable {l : ℕ} (hs : 2 * l ≤ 3 * (0 + q)) (hsm : 3 * (0 + q) ≤ 3 * l)
  (hsn : 3 * (0 + q) - 2 * l ≤ n) (d' : Data W π l)
  (hlj : l ≤ j) (hsj : 3 * (0 + q) - 2 * l ≤ j)
local notation "a'" => dividedPairLeft W (π ^ l) d'.b3 d'.b4 d'.b6
local notation "c'" => dividedPairRight W (π ^ l) d'.b3 d'.b4 d'.b6
local notation "left" => nodalShallowAmbientInput D hs hsm data hsn d' j hj hlj
local notation "right" => nodalIntermediateAmbientInput D hdepth hrk hrm data hr d j hj hkj
local notation "L" => nodalShallowAmbientOpen D hs hsm data hsn d' j hj hlj
local notation "N" => nodalIntermediateAmbientOpen D hdepth hrk hrm data hr d j hj hkj
local notation "fl" => nodalShallowAmbientAddition D hs hsm data hsn d' j hj hlj hsj
local notation "fr" => nodalIntermediateAmbientAddition D hdepth hrk hrm data hr d j hj hkj hrj

variable (hq : q ≤ n) (hqj : q ≤ j)
local notation "T" => tripleAmbientOpen D data hq j hj hqj
local notation "ft" => tripleAmbientAddition D data hq j hj hqj

variable {v : ℕ} (hv : v + v ≤ n) (dv : Data W π v) (hvj : v + v ≤ j)
local notation "Deep" => deepAmbientOpen D data hv dv j hj hvj
local notation "fd" => deepAmbientAddition D data hv dv j hj hvj
local notation "inc" => threeRegimeAmbientInput D hdepth hrk hrm data hr d
  j hj hkj hs hsm hsn d' hlj hq hqj
local notation "out" => threeRegimeAmbientLocal D hdepth hrk hrm data hr d
  j hj hkj hrj hs hsm hsn d' hlj hsj hq hqj
local notation "Three" => threeRegimeAmbientOpen D hdepth hrk hrm data hr d
  j hj hkj hs hsm hsn d' hlj hq hqj
local notation "fthree" => threeRegimeAmbientAddition D hdepth hrk hrm data hr d
  j hj hkj hrj hs hsm hsn d' hlj hsj hq hqj

/-- Every whole earlier ambient chart agrees with the whole deep ambient law. -/
theorem threeRegimeDeepAmbient_local (b : Option Bool) :
    pullback.fst (inc b) (Deep).ι ≫ out b =
      pullback.snd (inc b) (Deep).ι ≫ fd := by
  rcases b with _ | ⟨_ | _⟩
  · exact tripleDeepAmbient_pullback D data hv dv j hj hvj D hq hqj
  · exact shallowDeepAmbient_pullback D data hv dv j hj hvj hs hsm hsn d' hlj hsj
  · exact intermediateDeepAmbient_pullback
      D data hv dv j hj hvj hdepth hrk hrm hr d hkj hrj

/-- The entire three-regime union agrees on its full intersection with the deep extension. -/
theorem threeRegimeDeepAmbient_pullback :
    pullback.fst (Three).ι (Deep).ι ≫ fthree =
      pullback.snd (Three).ι (Deep).ι ≫ fd :=
  openImageUnionGlue_single_pullback inc out _ (Deep).ι fd
    (threeRegimeDeepAmbient_local D hdepth hrk hrm data hr d
      j hj hkj hrj hs hsm hsn d' hlj hsj hq hqj hv dv hvj)

/-- Equality holds for every source over the entire ambient intersection. -/
theorem threeRegimeDeepAmbient_overlap {X : Scheme}
    (p : X ⟶ (Three).toScheme) (q : X ⟶ (Deep).toScheme)
    (hpq : p ≫ (Three).ι = q ≫ (Deep).ι) : p ≫ fthree = q ≫ fd :=
  openImageUnionGlue_single_overlap inc out _ (Deep).ι fd
    (threeRegimeDeepAmbient_local D hdepth hrk hrm data hr d
      j hj hkj hrj hs hsm hsn d' hlj hsj hq hqj hv dv hvj) p q hpq

end FLT.Mazur.WeierstrassDividedDepth
