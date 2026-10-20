/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalIntermediateReciprocalExtendedPullback
public import FLT.Mazur.WeierstrassDividedUniversalSmoothPairPromotion

/-!
# Glue the universal intermediate law into the ambient resolved product

The universal tensor-pair smooth source is an actual open immersion. Its
constructed output glues with the old reciprocal-extended law on their entire
fiber-product intersection, producing a law on their ambient open union.
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

instance nodalIntermediateCommonInput_universal_open : IsOpenImmersion pair := by
  unfold nodalIntermediateCommonInput
  infer_instance

/-- The two actual domains of the ambient intermediate extension. -/
def nodalIntermediateAmbientChart (b : Bool) : Scheme :=
  if b then (V).toScheme else (Old).toScheme

/-- Both domains embed openly in precisely the same resolved product. -/
def nodalIntermediateAmbientInput : (b : Bool) →
    nodalIntermediateAmbientChart D hdepth hrk hrm data hr d j hj b ⟶
      finiteResolvedProduct hπ data j hj
  | false => (Old).ι
  | true => pair

instance nodalIntermediateAmbientInput_open (b : Bool) :
    IsOpenImmersion (nodalIntermediateAmbientInput D hdepth hrk hrm data hr d j hj hkj b) := by
  cases b <;> dsimp only [nodalIntermediateAmbientInput] <;> infer_instance

/-- The existing outputs, unchanged on their whole domains. -/
def nodalIntermediateAmbientLocal : (b : Bool) →
    nodalIntermediateAmbientChart D hdepth hrk hrm data hr d j hj b ⟶ (U).toScheme
  | false => finiteResolvedReciprocalExtendedPartialAddition hπ data j hj
  | true => nodalIntermediateCommonOutput D hdepth hrk hrm data hr d a c j hj hrj

local notation "inc" => nodalIntermediateAmbientInput D hdepth hrk hrm data hr d j hj hkj
local notation "out" => nodalIntermediateAmbientLocal D hdepth hrk hrm data hr d j hj hrj

/-- Both laws agree on every actual ambient intersection. -/
theorem nodalIntermediateAmbient_overlap (b b' : Bool) :
    pullback.fst (inc b) (inc b') ≫ out b = pullback.snd (inc b) (inc b') ≫ out b' := by
  cases b <;> cases b'
  · congr 1
    exact (cancel_mono (Old).ι).mp pullback.condition
  · exact nodalIntermediateCommonOutput_reciprocalExtendedPullback
      D hdepth hrk hrm data hr d a c j hj hkj hrj
  · exact (nodalIntermediateCommonOutput_reciprocalExtendedOverlap
      D hdepth hrk hrm data hr d a c j hj hkj hrj _ _ pullback.condition.symm).symm
  · congr 1
    exact (cancel_mono pair).mp pullback.condition

/-- The actual open union of the previous law and the universal intermediate law. -/
def nodalIntermediateAmbientOpen : (finiteResolvedProduct hπ data j hj).Opens :=
  openImageUnion inc

/-- The intermediate law and the whole previous law glue in the ambient resolved product. -/
def nodalIntermediateAmbientAddition :
    (nodalIntermediateAmbientOpen D hdepth hrk hrm data hr d j hj hkj).toScheme ⟶ (U).toScheme :=
  openImageUnionGlue inc out
    (nodalIntermediateAmbient_overlap D hdepth hrk hrm data hr d j hj hkj hrj)

/-- The ambient extension retains the entire reciprocal-extended law. -/
@[reassoc] theorem nodalIntermediateAmbientAddition_old :
    openImageUnionMap inc false ≫
        nodalIntermediateAmbientAddition D hdepth hrk hrm data hr d j hj hkj hrj =
      finiteResolvedReciprocalExtendedPartialAddition hπ data j hj :=
  openImageUnionGlue_fac _ _ _ false

/-- The ambient extension retains the entire constructed intermediate output. -/
@[reassoc] theorem nodalIntermediateAmbientAddition_intermediate :
    openImageUnionMap inc true ≫
        nodalIntermediateAmbientAddition D hdepth hrk hrm data hr d j hj hkj hrj =
      nodalIntermediateCommonOutput D hdepth hrk hrm data hr d a c j hj hrj :=
  openImageUnionGlue_fac _ _ _ true

/-- The ambient law remains over the original coefficient point of its first input. -/
@[reassoc] theorem nodalIntermediateAmbientAddition_structure :
    nodalIntermediateAmbientAddition D hdepth hrk hrm data hr d j hj hkj hrj ≫ t =
      (nodalIntermediateAmbientOpen D hdepth hrk hrm data hr d j hj hkj).ι ≫
        pullback.fst t t ≫ t := by
  apply openImageUnion_hom_ext inc
  intro b
  cases b
  · rw [nodalIntermediateAmbientAddition_old_assoc]
    exact (finiteResolvedReciprocalExtendedPartialAddition_structure hπ data j hj).trans
      (openImageUnionMap_fac_assoc inc false (pullback.fst t t ≫ t)).symm
  · rw [nodalIntermediateAmbientAddition_intermediate_assoc,
      nodalIntermediateCommonOutput_structure]
    exact (nodalIntermediateCommonInput_structure
      D hdepth hrk hrm data hr d a c j hj hkj).symm.trans
      (openImageUnionMap_fac_assoc inc true (pullback.fst t t ≫ t)).symm

/-- The same coefficient point is retained from the second input. -/
@[reassoc] theorem nodalIntermediateAmbientAddition_structure_snd :
    nodalIntermediateAmbientAddition D hdepth hrk hrm data hr d j hj hkj hrj ≫ t =
      (nodalIntermediateAmbientOpen D hdepth hrk hrm data hr d j hj hkj).ι ≫
        pullback.snd t t ≫ t := by
  rw [nodalIntermediateAmbientAddition_structure, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
