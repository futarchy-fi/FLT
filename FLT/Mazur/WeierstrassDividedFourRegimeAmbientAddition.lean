/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThreeRegimeDeepAmbientOverlap

/-!
# Glue the whole three-regime law with the deep ambient extension

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
local notation "Three" => threeRegimeAmbientOpen D hdepth hrk hrm data hr d
  j hj hkj hs hsm hsn d' hlj hq hqj
local notation "fthree" => threeRegimeAmbientAddition D hdepth hrk hrm data hr d
  j hj hkj hrj hs hsm hsn d' hlj hsj hq hqj

/-- The two entire ambient source schemes. -/
def fourRegimeAmbientChart (b : Bool) : Scheme :=
  if b then (Deep).toScheme else (Three).toScheme

/-- Both existing ambient domains embed openly in the same resolved product. -/
def fourRegimeAmbientInput : (b : Bool) →
    fourRegimeAmbientChart D hdepth hrk hrm data hr d j hj hkj
      hs hsm hsn d' hlj hq hqj hv dv hvj b ⟶ finiteResolvedProduct hπ data j hj
  | false => (Three).ι
  | true => (Deep).ι

local notation "inc" => fourRegimeAmbientInput D hdepth hrk hrm data hr d
  j hj hkj hs hsm hsn d' hlj hq hqj hv dv hvj

instance fourRegimeAmbientInput_open (b : Bool) :
    IsOpenImmersion (inc b) := by
  apply Bool.forall_bool.mpr ?_ b
  constructor <;> dsimp only [fourRegimeAmbientInput] <;> infer_instance

/-- Both constructed ambient laws on their whole existing domains. -/
def fourRegimeAmbientLocal : (b : Bool) →
    fourRegimeAmbientChart D hdepth hrk hrm data hr d j hj hkj
      hs hsm hsn d' hlj hq hqj hv dv hvj b ⟶ (U).toScheme
  | false => fthree
  | true => fd

local notation "out" => fourRegimeAmbientLocal D hdepth hrk hrm data hr d
  j hj hkj hrj hs hsm hsn d' hlj hsj hq hqj hv dv hvj

/-- All pairwise intersections carry the same constructed output. -/
theorem fourRegimeAmbient_compatible (b b' : Bool) :
    pullback.fst (inc b) (inc b') ≫ out b =
      pullback.snd (inc b) (inc b') ≫ out b' := by
  cases b <;> cases b'
  · exact congrArg (· ≫ fthree) ((cancel_mono (Three).ι).mp pullback.condition)
  · exact threeRegimeDeepAmbient_pullback D hdepth hrk hrm data hr d j hj hkj hrj
      hs hsm hsn d' hlj hsj hq hqj hv dv hvj
  · exact (threeRegimeDeepAmbient_overlap D hdepth hrk hrm data hr d j hj hkj hrj
      hs hsm hsn d' hlj hsj hq hqj hv dv hvj _ _ pullback.condition.symm).symm
  · exact congrArg (· ≫ fd) ((cancel_mono (Deep).ι).mp pullback.condition)

/-- The actual union of the two previous ambient domains. -/
def fourRegimeAmbientOpen : (finiteResolvedProduct hπ data j hj).Opens :=
  openImageUnion inc

local notation "Union" => fourRegimeAmbientOpen D hdepth hrk hrm data hr d
  j hj hkj hs hsm hsn d' hlj hq hqj hv dv hvj

/-- The two actual ambient laws glue on their full union. -/
def fourRegimeAmbientAddition : (Union).toScheme ⟶ (U).toScheme :=
  openImageUnionGlue inc out (fourRegimeAmbient_compatible
    D hdepth hrk hrm data hr d j hj hkj hrj
      hs hsm hsn d' hlj hsj hq hqj hv dv hvj)

local notation "law" => fourRegimeAmbientAddition D hdepth hrk hrm data hr d
  j hj hkj hrj hs hsm hsn d' hlj hsj hq hqj hv dv hvj

/-- The entire three-regime ambient extension is preserved. -/
@[reassoc] theorem fourRegimeAmbientAddition_three :
    openImageUnionMap inc false ≫ law = fthree := openImageUnionGlue_fac _ _ _ false

/-- The entire deep ambient extension is preserved. -/
@[reassoc] theorem fourRegimeAmbientAddition_deep :
    openImageUnionMap inc true ≫ law = fd := openImageUnionGlue_fac _ _ _ true

/-- The domain is exactly the union of both previous ambient opens. -/
theorem fourRegimeAmbientOpen_eq : Union = Three ⊔ Deep := by
  simp only [fourRegimeAmbientOpen, openImageUnion, iSup_bool_eq,
    fourRegimeAmbientInput, Scheme.Opens.opensRange_ι, sup_comm]

/-- The glued law retains the coefficient point of the first input. -/
@[reassoc] theorem fourRegimeAmbientAddition_structure :
    law ≫ t = (Union).ι ≫ pullback.fst t t ≫ t := by
  apply openImageUnion_hom_ext inc
  intro b
  cases b
  · rw [fourRegimeAmbientAddition_three_assoc,
      threeRegimeAmbientAddition_structure]
    exact (openImageUnionMap_fac_assoc inc false (pullback.fst t t ≫ t)).symm
  · rw [fourRegimeAmbientAddition_deep_assoc,
      deepAmbientAddition_structure]
    exact (openImageUnionMap_fac_assoc inc true (pullback.fst t t ≫ t)).symm

/-- The same coefficient point is retained from the second input. -/
@[reassoc] theorem fourRegimeAmbientAddition_structure_snd :
    law ≫ t = (Union).ι ≫ pullback.snd t t ≫ t := by
  rw [fourRegimeAmbientAddition_structure, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
