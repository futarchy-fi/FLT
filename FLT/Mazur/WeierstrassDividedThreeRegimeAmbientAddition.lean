/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalShallowIntermediateAmbientAddition
public import FLT.Mazur.WeierstrassDividedShallowTripleAmbientOverlap
public import FLT.Mazur.WeierstrassDividedTripleIntermediateAmbientOverlap

/-!
# Glue shallow, intermediate and exact-triple ambient extensions

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

/-- Index the three actual ambient domains. -/
def threeRegimeAmbientChart : Option Bool → Scheme
  | none => (T).toScheme
  | some false => (L).toScheme
  | some true => (N).toScheme

/-- Each whole domain embeds in the common resolved product. -/
def threeRegimeAmbientInput : (b : Option Bool) →
    threeRegimeAmbientChart D hdepth hrk hrm data hr d
  j hj hkj hs hsm hsn d' hlj hq hqj b ⟶ finiteResolvedProduct hπ data j hj
  | none => (T).ι
  | some false => (L).ι
  | some true => (N).ι

local notation "inc" => threeRegimeAmbientInput D hdepth hrk hrm data hr d
  j hj hkj hs hsm hsn d' hlj hq hqj

instance threeRegimeAmbientInput_open (b : Option Bool) : IsOpenImmersion (inc b) := by
  cases b with
  | none => dsimp only [threeRegimeAmbientInput]; infer_instance
  | some b => cases b <;> dsimp only [threeRegimeAmbientInput] <;> infer_instance

/-- The three constructed laws on their entire existing domains. -/
def threeRegimeAmbientLocal : (b : Option Bool) →
    threeRegimeAmbientChart D hdepth hrk hrm data hr d
  j hj hkj hs hsm hsn d' hlj hq hqj b ⟶ (U).toScheme
  | none => ft
  | some false => fl
  | some true => fr

local notation "out" => threeRegimeAmbientLocal D hdepth hrk hrm data hr d
  j hj hkj hrj hs hsm hsn d' hlj hsj hq hqj

/-- Every ordered intersection has equal outputs. -/
theorem threeRegimeAmbient_compatible (b b' : Option Bool) :
    pullback.fst (inc b) (inc b') ≫ out b =
      pullback.snd (inc b) (inc b') ≫ out b' := by
  rcases b with _ | ⟨_ | _⟩ <;> rcases b' with _ | ⟨_ | _⟩
  · exact congrArg (· ≫ ft) ((cancel_mono (T).ι).mp pullback.condition)
  · exact (shallowTripleAmbient_overlap D data hq j hj hqj
      hs hsm hsn d' hlj hsj _ _ pullback.condition.symm).symm
  · exact tripleIntermediateAmbient_pullback
      D hdepth hrk hrm data hr d j hj hkj hrj D hq hqj
  · exact shallowTripleAmbient_pullback D data hq j hj hqj hs hsm hsn d' hlj hsj
  · exact congrArg (· ≫ fl) ((cancel_mono (L).ι).mp pullback.condition)
  · exact nodalShallowIntermediateAmbient_pullback D hdepth hrk hrm data hr d j hj hkj hrj
      hs hsm hsn d' hlj hsj
  · exact (tripleIntermediateAmbient_overlap
      D hdepth hrk hrm data hr d j hj hkj hrj D hq hqj _ _ pullback.condition.symm).symm
  · exact (nodalShallowIntermediateAmbient_overlap D hdepth hrk hrm data hr d j hj hkj hrj
      hs hsm hsn d' hlj hsj _ _ pullback.condition.symm).symm
  · exact congrArg (· ≫ fr) ((cancel_mono (N).ι).mp pullback.condition)

/-- The union of the three actual ambient domains. -/
def threeRegimeAmbientOpen : (finiteResolvedProduct hπ data j hj).Opens :=
  openImageUnion inc

local notation "Union" => threeRegimeAmbientOpen D hdepth hrk hrm data hr d
  j hj hkj hs hsm hsn d' hlj hq hqj

/-- The three actual laws glue over the whole union. -/
def threeRegimeAmbientAddition : (Union).toScheme ⟶ (U).toScheme :=
  openImageUnionGlue inc out (threeRegimeAmbient_compatible D hdepth hrk hrm data hr d
  j hj hkj hrj hs hsm hsn d' hlj hsj hq hqj)

local notation "law" => threeRegimeAmbientAddition D hdepth hrk hrm data hr d
  j hj hkj hrj hs hsm hsn d' hlj hsj hq hqj

/-- The whole exact-triple ambient law is retained. -/
@[reassoc] theorem threeRegimeAmbientAddition_triple :
    openImageUnionMap inc none ≫ law = ft := openImageUnionGlue_fac _ _ _ none

/-- The whole shallow ambient law is retained. -/
@[reassoc] theorem threeRegimeAmbientAddition_shallow :
    openImageUnionMap inc (some false) ≫ law = fl := openImageUnionGlue_fac _ _ _ _

/-- The whole intermediate ambient law is retained. -/
@[reassoc] theorem threeRegimeAmbientAddition_intermediate :
    openImageUnionMap inc (some true) ≫ law = fr := openImageUnionGlue_fac _ _ _ _

/-- The domain is exactly the union of the three original ambient opens. -/
theorem threeRegimeAmbientOpen_eq : Union = T ⊔ (L ⊔ N) := by
  simp only [threeRegimeAmbientOpen, openImageUnion, iSup_option, iSup_bool_eq,
    threeRegimeAmbientInput, Scheme.Opens.opensRange_ι, sup_comm, sup_left_comm, sup_assoc]

/-- The union law preserves the coefficient point of the first input. -/
@[reassoc] theorem threeRegimeAmbientAddition_structure :
    law ≫ t = (Union).ι ≫ pullback.fst t t ≫ t := by
  apply openImageUnion_hom_ext inc
  intro b
  rcases b with _ | ⟨_ | _⟩
  · rw [threeRegimeAmbientAddition_triple_assoc, tripleAmbientAddition_structure]
    exact (openImageUnionMap_fac_assoc inc none (pullback.fst t t ≫ t)).symm
  · rw [threeRegimeAmbientAddition_shallow_assoc, nodalShallowAmbientAddition_structure]
    exact (openImageUnionMap_fac_assoc inc (some false) (pullback.fst t t ≫ t)).symm
  · rw [threeRegimeAmbientAddition_intermediate_assoc,
      nodalIntermediateAmbientAddition_structure]
    exact (openImageUnionMap_fac_assoc inc (some true) (pullback.fst t t ≫ t)).symm

/-- The second input has the same coefficient point. -/
@[reassoc] theorem threeRegimeAmbientAddition_structure_snd :
    law ≫ t = (Union).ι ≫ pullback.snd t t ≫ t := by
  rw [threeRegimeAmbientAddition_structure, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
