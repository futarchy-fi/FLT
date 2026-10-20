/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleReciprocalExtendedPullback
public import FLT.Mazur.WeierstrassDividedUniversalSmoothPairPromotion

/-!
# Glue the universal exact-triple law into the ambient resolved product

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
  {W : WeierstrassCurve R} {π : R} {start n k : ℕ}
  (D : SplitNodeDepth W π (3 * (start + k)))
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
variable (j : ℕ) (hj : j ≤ n) (hkj : k ≤ j)
local notation "a" => dividedPairLeft W (π ^ (start + k)) (d).b3 (d).b4 (d).b6
local notation "c" => dividedPairRight W (π ^ (start + k)) (d).b3 (d).b4 (d).b6
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

instance tripleCommonInput_universal_open : IsOpenImmersion pair := by
  unfold tripleCommonInput
  infer_instance

/-- The two actual domains of the ambient exact-triple extension. -/
def tripleAmbientChart (b : Bool) : Scheme :=
  if b then (V).toScheme else (Old).toScheme

/-- Both domains embed openly in precisely the same resolved product. -/
def tripleAmbientInput : (b : Bool) →
    tripleAmbientChart D data hk j hj b ⟶
      finiteResolvedProduct hπ data j hj
  | false => (Old).ι
  | true => pair

instance tripleAmbientInput_open (b : Bool) :
    IsOpenImmersion (tripleAmbientInput D data hk j hj hkj b) := by
  cases b <;> dsimp only [tripleAmbientInput] <;> infer_instance

/-- The existing outputs, unchanged on their whole domains. -/
def tripleAmbientLocal : (b : Bool) →
    tripleAmbientChart D data hk j hj b ⟶ (U).toScheme
  | false => finiteResolvedReciprocalExtendedPartialAddition hπ data j hj
  | true => tripleCommonOutput D data hk a c j hj hkj

local notation "inc" => tripleAmbientInput D data hk j hj hkj
local notation "out" => tripleAmbientLocal D data hk j hj hkj

/-- Both laws agree on every actual ambient intersection. -/
theorem tripleAmbient_overlap (b b' : Bool) :
    pullback.fst (inc b) (inc b') ≫ out b = pullback.snd (inc b) (inc b') ≫ out b' := by
  cases b <;> cases b'
  · exact congrArg (· ≫ finiteResolvedReciprocalExtendedPartialAddition hπ data j hj)
      ((cancel_mono (Old).ι).mp pullback.condition)
  · exact tripleCommonOutput_reciprocalExtendedPullback
      D data hk a c j hj hkj
  · exact (tripleCommonOutput_reciprocalExtendedOverlap
      D data hk a c j hj hkj _ _ pullback.condition.symm).symm
  · exact congrArg (· ≫ tripleCommonOutput D data hk a c j hj hkj)
      ((cancel_mono pair).mp pullback.condition)

/-- The actual open union of the previous law and the universal exact-triple law. -/
def tripleAmbientOpen : (finiteResolvedProduct hπ data j hj).Opens :=
  openImageUnion inc

/-- The exact-triple law and the whole previous law glue in the ambient resolved product. -/
def tripleAmbientAddition :
    (tripleAmbientOpen D data hk j hj hkj).toScheme ⟶ (U).toScheme :=
  openImageUnionGlue inc out
    (tripleAmbient_overlap D data hk j hj hkj)

/-- The ambient extension retains the entire reciprocal-extended law. -/
@[reassoc] theorem tripleAmbientAddition_old :
    openImageUnionMap inc false ≫
        tripleAmbientAddition D data hk j hj hkj =
      finiteResolvedReciprocalExtendedPartialAddition hπ data j hj :=
  openImageUnionGlue_fac _ _ _ false

/-- The ambient extension retains the entire constructed exact-triple output. -/
@[reassoc] theorem tripleAmbientAddition_triple :
    openImageUnionMap inc true ≫
        tripleAmbientAddition D data hk j hj hkj =
      tripleCommonOutput D data hk a c j hj hkj :=
  openImageUnionGlue_fac _ _ _ true

/-- The ambient law remains over the original coefficient point of its first input. -/
@[reassoc] theorem tripleAmbientAddition_structure :
    tripleAmbientAddition D data hk j hj hkj ≫ t =
      (tripleAmbientOpen D data hk j hj hkj).ι ≫
        pullback.fst t t ≫ t := by
  apply openImageUnion_hom_ext inc
  intro b
  cases b
  · rw [tripleAmbientAddition_old_assoc]
    exact (finiteResolvedReciprocalExtendedPartialAddition_structure hπ data j hj).trans
      (openImageUnionMap_fac_assoc inc false (pullback.fst t t ≫ t)).symm
  · rw [tripleAmbientAddition_triple_assoc,
      tripleCommonOutput_structure]
    exact (tripleCommonInput_structure
      D data hk a c j hj hkj).symm.trans
      (openImageUnionMap_fac_assoc inc true (pullback.fst t t ≫ t)).symm

/-- The same coefficient point is retained from the second input. -/
@[reassoc] theorem tripleAmbientAddition_structure_snd :
    tripleAmbientAddition D data hk j hj hkj ≫ t =
      (tripleAmbientOpen D data hk j hj hkj).ι ≫
        pullback.snd t t ≫ t := by
  rw [tripleAmbientAddition_structure, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
