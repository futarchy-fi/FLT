/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThreeRegimeAmbientAddition

/-!
# Retain the whole previously glued shallow/intermediate extension

The three entire ambient domains carry one law on their actual open union.
All comparisons come from the literal formula covers of the original laws.
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

local notation "Prior" => nodalShallowIntermediateAmbientOpen D hdepth hrk hrm data hr d
  j hj hkj hs hsm hsn d' hlj
local notation "priorLaw" => nodalShallowIntermediateAmbientAddition D hdepth hrk hrm data hr d
  j hj hkj hrj hs hsm hsn d' hlj hsj
local notation "oldInc" => nodalShallowIntermediateAmbientInput D hdepth hrk hrm data hr d
  j hj hkj hs hsm hsn d' hlj
local notation "Union" => threeRegimeAmbientOpen D hdepth hrk hrm data hr d
  j hj hkj hs hsm hsn d' hlj hq hqj
local notation "law" => threeRegimeAmbientAddition D hdepth hrk hrm data hr d
  j hj hkj hrj hs hsm hsn d' hlj hsj hq hqj
local notation "newInc" => threeRegimeAmbientInput D hdepth hrk hrm data hr d
  j hj hkj hs hsm hsn d' hlj hq hqj

/-- The new domain contains the entire prior glued extension. -/
theorem threeRegimeAmbientOpen_prior_le : Prior ≤ Union := by
  rw [nodalShallowIntermediateAmbientOpen_eq, threeRegimeAmbientOpen_eq]
  exact le_sup_right

/-- Include the whole prior shallow/intermediate domain in the three-regime domain. -/
def threeRegimePriorInclusion : (Prior).toScheme ⟶ (Union).toScheme :=
  Scheme.homOfLE _ (threeRegimeAmbientOpen_prior_le D hdepth hrk hrm data hr d
    j hj hkj hs hsm hsn d' hlj hq hqj)

local notation "prior" => threeRegimePriorInclusion D hdepth hrk hrm data hr d
  j hj hkj hs hsm hsn d' hlj hq hqj

/-- The comparison of domains is the literal ambient inclusion. -/
@[reassoc] theorem threeRegimePriorInclusion_ι : prior ≫ (Union).ι = (Prior).ι :=
  Scheme.homOfLE_ι _ _

/-- The shallow chart has its unchanged map into the larger domain. -/
@[reassoc] theorem threeRegimePriorInclusion_shallow :
    openImageUnionMap oldInc false ≫ prior = openImageUnionMap newInc (some false) := by
  apply (cancel_mono (Union).ι).mp
  rw [Category.assoc, threeRegimePriorInclusion_ι]
  exact (openImageUnionMap_fac oldInc false).trans
    (openImageUnionMap_fac newInc (some false)).symm

/-- The intermediate chart has its unchanged map into the larger domain. -/
@[reassoc] theorem threeRegimePriorInclusion_intermediate :
    openImageUnionMap oldInc true ≫ prior = openImageUnionMap newInc (some true) := by
  apply (cancel_mono (Union).ι).mp
  rw [Category.assoc, threeRegimePriorInclusion_ι]
  exact (openImageUnionMap_fac oldInc true).trans
    (openImageUnionMap_fac newInc (some true)).symm

/-- The whole earlier glued law is retained, including its original overlap. -/
@[reassoc] theorem threeRegimeAmbientAddition_prior : prior ≫ law = priorLaw := by
  apply openImageUnion_hom_ext oldInc
  intro b
  cases b
  · rw [threeRegimePriorInclusion_shallow_assoc, threeRegimeAmbientAddition_shallow,
      nodalShallowIntermediateAmbientAddition_shallow]
  · rw [threeRegimePriorInclusion_intermediate_assoc, threeRegimeAmbientAddition_intermediate,
      nodalShallowIntermediateAmbientAddition_intermediate]

/-- The enlarged domain is precisely the exact-triple domain union the whole prior domain. -/
theorem threeRegimeAmbientOpen_eq_prior : Union = T ⊔ Prior := by
  rw [threeRegimeAmbientOpen_eq, nodalShallowIntermediateAmbientOpen_eq]

end FLT.Mazur.WeierstrassDividedDepth
