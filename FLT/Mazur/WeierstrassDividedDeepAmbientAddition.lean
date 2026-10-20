/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDeepReciprocalExtendedPullback
public import FLT.Mazur.WeierstrassDividedUniversalSmoothPairPromotion

/-!
# Glue the universal deep-node law into the ambient resolved product

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
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ}
  (D : SplitNodeDepth W π m)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hkk : k + k ≤ n)
  (d : Data W π k)
variable (j : ℕ) (hj : j ≤ n) (hkj : k + k ≤ j)
local notation "a" => dividedPairLeft W (π ^ k) (d).b3 (d).b4 (d).b6
local notation "c" => dividedPairRight W (π ^ k) (d).b3 (d).b4 (d).b6
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "O" => nodalDeepAdditionOpen D data hkk d a c
local notation "P" => suppliedDividedSmoothInputOpen d a c

local notation "V" => deepSmoothSourceOpen D data hkk d a c
local notation "pair" => deepCommonInput D data hkk d a c j hj hkj
local notation "Old" => finiteResolvedReciprocalExtendedOpen hπ data j hj
local notation "i" => finiteResolvedReciprocalExtendedInput hπ data j hj

instance deepCommonInput_universal_open : IsOpenImmersion pair := by
  unfold deepCommonInput
  infer_instance

/-- The two actual domains of the ambient deep-node extension. -/
def deepAmbientChart (b : Bool) : Scheme :=
  if b then (V).toScheme else (Old).toScheme

/-- Both domains embed openly in precisely the same resolved product. -/
def deepAmbientInput : (b : Bool) →
    deepAmbientChart D data hkk d j hj b ⟶
      finiteResolvedProduct hπ data j hj
  | false => (Old).ι
  | true => pair

instance deepAmbientInput_open (b : Bool) :
    IsOpenImmersion (deepAmbientInput D data hkk d j hj hkj b) := by
  cases b <;> dsimp only [deepAmbientInput] <;> infer_instance

/-- The existing outputs, unchanged on their whole domains. -/
def deepAmbientLocal : (b : Bool) →
    deepAmbientChart D data hkk d j hj b ⟶ (U).toScheme
  | false => finiteResolvedReciprocalExtendedPartialAddition hπ data j hj
  | true => deepCommonOutput D data hkk d a c j hj hkj

local notation "inc" => deepAmbientInput D data hkk d j hj hkj
local notation "out" => deepAmbientLocal D data hkk d j hj hkj

/-- Both laws agree on every actual ambient intersection. -/
theorem deepAmbient_overlap (b b' : Bool) :
    pullback.fst (inc b) (inc b') ≫ out b = pullback.snd (inc b) (inc b') ≫ out b' := by
  cases b <;> cases b'
  · exact congrArg (· ≫ finiteResolvedReciprocalExtendedPartialAddition hπ data j hj)
      ((cancel_mono (Old).ι).mp pullback.condition)
  · exact deepCommonOutput_reciprocalExtendedPullback
      D data hkk d a c j hj hkj
  · exact (deepCommonOutput_reciprocalExtendedOverlap
      D data hkk d a c j hj hkj _ _ pullback.condition.symm).symm
  · exact congrArg (· ≫ deepCommonOutput D data hkk d a c j hj hkj)
      ((cancel_mono pair).mp pullback.condition)

/-- The actual open union of the previous law and the universal deep-node law. -/
def deepAmbientOpen : (finiteResolvedProduct hπ data j hj).Opens :=
  openImageUnion inc

/-- The deep-node law and the whole previous law glue in the ambient resolved product. -/
def deepAmbientAddition :
    (deepAmbientOpen D data hkk d j hj hkj).toScheme ⟶ (U).toScheme :=
  openImageUnionGlue inc out
    (deepAmbient_overlap D data hkk d j hj hkj)

/-- The ambient extension retains the entire reciprocal-extended law. -/
@[reassoc] theorem deepAmbientAddition_old :
    openImageUnionMap inc false ≫
        deepAmbientAddition D data hkk d j hj hkj =
      finiteResolvedReciprocalExtendedPartialAddition hπ data j hj :=
  openImageUnionGlue_fac _ _ _ false

/-- The ambient extension retains the entire constructed deep-node output. -/
@[reassoc] theorem deepAmbientAddition_deep :
    openImageUnionMap inc true ≫
        deepAmbientAddition D data hkk d j hj hkj =
      deepCommonOutput D data hkk d a c j hj hkj :=
  openImageUnionGlue_fac _ _ _ true

/-- The ambient law remains over the original coefficient point of its first input. -/
@[reassoc] theorem deepAmbientAddition_structure :
    deepAmbientAddition D data hkk d j hj hkj ≫ t =
      (deepAmbientOpen D data hkk d j hj hkj).ι ≫
        pullback.fst t t ≫ t := by
  apply openImageUnion_hom_ext inc
  intro b
  cases b
  · rw [deepAmbientAddition_old_assoc]
    exact (finiteResolvedReciprocalExtendedPartialAddition_structure hπ data j hj).trans
      (openImageUnionMap_fac_assoc inc false (pullback.fst t t ≫ t)).symm
  · rw [deepAmbientAddition_deep_assoc,
      deepCommonOutput_structure]
    exact (deepCommonInput_structure
      D data hkk d a c j hj hkj).symm.trans
      (openImageUnionMap_fac_assoc inc true (pullback.fst t t ≫ t)).symm

/-- The same coefficient point is retained from the second input. -/
@[reassoc] theorem deepAmbientAddition_structure_snd :
    deepAmbientAddition D data hkk d j hj hkj ≫ t =
      (deepAmbientOpen D data hkk d j hj hkj).ι ≫
        pullback.snd t t ≫ t := by
  rw [deepAmbientAddition_structure, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
