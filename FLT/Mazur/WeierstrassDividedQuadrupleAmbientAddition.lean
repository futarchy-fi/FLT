/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedQuadrupleReciprocalExtendedPullback
public import FLT.Mazur.WeierstrassDividedUniversalSmoothPairPromotion

/-!
# Glue the universal quadruple-depth law into the ambient resolved product

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
  {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (D : SplitNodeDepth W π (4 * k)) (d : Data W π k)
local notation "data" => splitNodeDoubledFamily D
local notation "j" => k + k
local notation "hj" => (le_rfl : k + k ≤ k + k)
local notation "a" => dividedPairLeft W (π ^ k) (d).b3 (d).b4 (d).b6
local notation "c" => dividedPairRight W (π ^ k) (d).b3 (d).b4 (d).b6
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "O" => nodalQuadrupleAdditionOpen D d a c
local notation "P" => suppliedDividedSmoothInputOpen d a c

local notation "V" => quadrupleSmoothSourceOpen D d a c
local notation "pair" => quadrupleCommonInput D d a c
local notation "Old" => finiteResolvedReciprocalExtendedOpen hπ data j hj
local notation "i" => finiteResolvedReciprocalExtendedInput hπ data j hj

instance quadrupleCommonInput_universal_open : IsOpenImmersion pair := by
  unfold quadrupleCommonInput
  infer_instance

/-- The two actual domains of the ambient quadruple-depth extension. -/
def quadrupleAmbientChart (b : Bool) : Scheme :=
  if b then (V).toScheme else (Old).toScheme

/-- Both domains embed openly in precisely the same resolved product. -/
def quadrupleAmbientInput : (b : Bool) →
    quadrupleAmbientChart D d b ⟶
      finiteResolvedProduct hπ data j hj
  | false => (Old).ι
  | true => pair

instance quadrupleAmbientInput_open (b : Bool) :
    IsOpenImmersion (quadrupleAmbientInput D d b) := by
  cases b <;> dsimp only [quadrupleAmbientInput] <;> infer_instance

/-- The existing outputs, unchanged on their whole domains. -/
def quadrupleAmbientLocal : (b : Bool) →
    quadrupleAmbientChart D d b ⟶ (U).toScheme
  | false => finiteResolvedReciprocalExtendedPartialAddition hπ data j hj
  | true => quadrupleCommonOutput D d a c

local notation "inc" => quadrupleAmbientInput D d
local notation "out" => quadrupleAmbientLocal D d

/-- Both laws agree on every actual ambient intersection. -/
theorem quadrupleAmbient_overlap (b b' : Bool) :
    pullback.fst (inc b) (inc b') ≫ out b = pullback.snd (inc b) (inc b') ≫ out b' := by
  cases b <;> cases b'
  · exact congrArg (· ≫ finiteResolvedReciprocalExtendedPartialAddition hπ data j hj)
      ((cancel_mono (Old).ι).mp pullback.condition)
  · exact quadrupleCommonOutput_reciprocalExtendedPullback
      D d a c
  · exact (quadrupleCommonOutput_reciprocalExtendedOverlap
      D d a c _ _ pullback.condition.symm).symm
  · exact congrArg (· ≫ quadrupleCommonOutput D d a c)
      ((cancel_mono pair).mp pullback.condition)

/-- The actual open union of the previous law and the universal quadruple-depth law. -/
def quadrupleAmbientOpen : (finiteResolvedProduct hπ data j hj).Opens :=
  openImageUnion inc

/-- The quadruple-depth law and the whole previous law glue in the ambient resolved product. -/
def quadrupleAmbientAddition :
    (quadrupleAmbientOpen D d).toScheme ⟶ (U).toScheme :=
  openImageUnionGlue inc out
    (quadrupleAmbient_overlap D d)

/-- The ambient extension retains the entire reciprocal-extended law. -/
@[reassoc] theorem quadrupleAmbientAddition_old :
    openImageUnionMap inc false ≫
        quadrupleAmbientAddition D d =
      finiteResolvedReciprocalExtendedPartialAddition hπ data j hj :=
  openImageUnionGlue_fac _ _ _ false

/-- The ambient extension retains the entire constructed quadruple-depth output. -/
@[reassoc] theorem quadrupleAmbientAddition_quadruple :
    openImageUnionMap inc true ≫
        quadrupleAmbientAddition D d =
      quadrupleCommonOutput D d a c :=
  openImageUnionGlue_fac _ _ _ true

/-- The ambient law remains over the original coefficient point of its first input. -/
@[reassoc] theorem quadrupleAmbientAddition_structure :
    quadrupleAmbientAddition D d ≫ t =
      (quadrupleAmbientOpen D d).ι ≫
        pullback.fst t t ≫ t := by
  apply openImageUnion_hom_ext inc
  intro b
  cases b
  · rw [quadrupleAmbientAddition_old_assoc]
    exact (finiteResolvedReciprocalExtendedPartialAddition_structure hπ data j hj).trans
      (openImageUnionMap_fac_assoc inc false (pullback.fst t t ≫ t)).symm
  · rw [quadrupleAmbientAddition_quadruple_assoc,
      quadrupleCommonOutput_structure]
    exact (quadrupleCommonInput_structure
      D d a c).symm.trans
      (openImageUnionMap_fac_assoc inc true (pullback.fst t t ≫ t)).symm

/-- The same coefficient point is retained from the second input. -/
@[reassoc] theorem quadrupleAmbientAddition_structure_snd :
    quadrupleAmbientAddition D d ≫ t =
      (quadrupleAmbientOpen D d).ι ≫
        pullback.snd t t ≫ t := by
  rw [quadrupleAmbientAddition_structure, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
