/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedQuadrupleTripleOverlap
public import FLT.Mazur.WeierstrassDividedQuadrupleAmbientAddition
public import FLT.Mazur.WeierstrassDividedTripleAmbientAddition
public import FLT.Mazur.OpenImmersionImageUnionGluedOverlap

/-!
# Compare the entire triple and quadruple-depth ambient extensions

The literal four pairwise intersections cover the full overlap. The new
cross-depth comparison handles the triple/quadruple-depth chart intersection.
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
local notation "a" => dividedPairLeft W (π ^ k) d.b3 d.b4 d.b6
local notation "c" => dividedPairRight W (π ^ k) d.b3 d.b4 d.b6
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

variable {l : ℕ} (D' : SplitNodeDepth W π (3 * (0 + l))) (hl : l ≤ k + k)
local notation "d'" => data ⟨l, Nat.lt_succ_of_le hl⟩
variable (hlj : l ≤ k + k)
local notation "a'" => dividedPairLeft W (π ^ (0 + l)) (d').b3 (d').b4 (d').b6
local notation "c'" => dividedPairRight W (π ^ (0 + l)) (d').b3 (d').b4 (d').b6
local notation "left" => tripleAmbientInput D' data hl j hj hlj
local notation "right" => quadrupleAmbientInput D d
local notation "L" => tripleAmbientOpen D' data hl j hj hlj
local notation "N" => quadrupleAmbientOpen D d
local notation "fl" => tripleAmbientAddition D' data hl j hj hlj
local notation "fr" => quadrupleAmbientAddition D d

local notation "ol" => tripleAmbientLocal D' data hl j hj hlj
local notation "orr" => quadrupleAmbientLocal D d

/-- The old/quadruple-depth literal intersection has its constructed comparison. -/
theorem tripleQuadrupleAmbient_oldQuadruple :
    pullback.fst (left false) (right true) ≫ ol false =
      pullback.snd (left false) (right true) ≫ orr true :=
  quadrupleCommonOutput_reciprocalExtendedOverlap
    D d a c _ _ pullback.condition

/-- The triple/old literal intersection has its constructed comparison. -/
theorem tripleQuadrupleAmbient_tripleOld :
    pullback.fst (left true) (right false) ≫ ol true =
      pullback.snd (left true) (right false) ≫ orr false :=
  (tripleCommonOutput_reciprocalExtendedOverlap
    D' data hl a' c' j hj hlj _ _ pullback.condition.symm).symm

/-- The new/new literal intersection uses the full cross-depth comparison. -/
theorem tripleQuadrupleAmbient_newIntersection :
    pullback.fst (left true) (right true) ≫ ol true =
      pullback.snd (left true) (right true) ≫ orr true :=
  quadrupleCommonOutput_tripleOverlap D d a c
    D' hl a' c' hlj _ _ pullback.condition

/-- The common old chart agrees with itself. -/
theorem tripleQuadrupleAmbient_oldOld :
    pullback.fst (left false) (right false) ≫ ol false =
      pullback.snd (left false) (right false) ≫ orr false := by
  exact congrArg (· ≫ finiteResolvedReciprocalExtendedPartialAddition hπ data j hj)
    ((cancel_mono (Old).ι).mp pullback.condition)

/-- All four literal chart intersections have equal constructed outputs. -/
theorem tripleQuadrupleAmbient_local (b b' : Bool) :
    pullback.fst (left b) (right b') ≫ ol b =
      pullback.snd (left b) (right b') ≫ orr b' := by
  cases b <;> cases b'
  · exact tripleQuadrupleAmbient_oldOld
      D d D' hl hlj
  · exact tripleQuadrupleAmbient_oldQuadruple
      D d D' hl hlj
  · exact tripleQuadrupleAmbient_tripleOld
      D d D' hl hlj
  · exact tripleQuadrupleAmbient_newIntersection
      D d D' hl hlj

/-- The two entire ambient extensions agree on their actual full fiber product. -/
theorem tripleQuadrupleAmbient_pullback :
    pullback.fst (L).ι (N).ι ≫ fl = pullback.snd (L).ι (N).ι ≫ fr :=
  openImageUnionGlue_pullback_eq left right ol orr _ _
    (tripleQuadrupleAmbient_local D d
      D' hl hlj)

/-- Every common-source comparison follows from the full fiber-product equality. -/
theorem tripleQuadrupleAmbient_overlap {X : Scheme}
    (p : X ⟶ (L).toScheme) (q : X ⟶ (N).toScheme)
    (hpq : p ≫ (L).ι = q ≫ (N).ι) : p ≫ fl = q ≫ fr := by
  have h := congrArg (pullback.lift p q hpq ≫ ·)
    (tripleQuadrupleAmbient_pullback D d
      D' hl hlj)
  simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using h

end FLT.Mazur.WeierstrassDividedDepth
