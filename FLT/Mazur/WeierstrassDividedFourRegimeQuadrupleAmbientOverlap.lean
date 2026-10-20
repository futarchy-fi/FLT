/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourRegimeAmbientAddition
public import FLT.Mazur.WeierstrassDividedShallowQuadrupleAmbientOverlap
public import FLT.Mazur.WeierstrassDividedTripleQuadrupleAmbientOverlap
public import FLT.Mazur.WeierstrassDividedIntermediateQuadrupleAmbientOverlap
public import FLT.Mazur.WeierstrassDividedDeepQuadrupleAmbientOverlap

/-!
# Compare the whole four-regime law with the quadruple extension

Use the actual doubled-depth family as the common model. Every entire earlier
ambient law compares with the quadruple extension through its formula cover.
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

variable {q i r l v : ℕ} (D' : SplitNodeDepth W π (3 * (0 + q)))
  (hi : 3 * i ≤ 3 * (0 + q)) (hri : r ≤ i) (hrm : r ≤ 3 * (0 + q) - 3 * i)
  (hir : i + r ≤ k + k) (di : Data W π i) (hij : i ≤ k + k)
  (hs : 2 * l ≤ 3 * (0 + q)) (hsm : 3 * (0 + q) ≤ 3 * l)
  (hsn : 3 * (0 + q) - 2 * l ≤ k + k) (dl : Data W π l) (hlj : l ≤ k + k)
  (hq : q ≤ k + k) (hv : v + v ≤ k + k) (dv : Data W π v)
local notation "Three" => threeRegimeAmbientOpen D' hi hri hrm data hir di
  j hj hij hs hsm hsn dl hlj hq hq
local notation "fthree" => threeRegimeAmbientAddition D' hi hri hrm data hir di
  j hj hij hir hs hsm hsn dl hlj hsn hq hq
local notation "incThree" => threeRegimeAmbientInput D' hi hri hrm data hir di
  j hj hij hs hsm hsn dl hlj hq hq
local notation "outThree" => threeRegimeAmbientLocal D' hi hri hrm data hir di
  j hj hij hir hs hsm hsn dl hlj hsn hq hq
local notation "Four" => fourRegimeAmbientOpen D' hi hri hrm data hir di
  j hj hij hs hsm hsn dl hlj hq hq hv dv hv
local notation "ffour" => fourRegimeAmbientAddition D' hi hri hrm data hir di
  j hj hij hir hs hsm hsn dl hlj hsn hq hq hv dv hv
local notation "incFour" => fourRegimeAmbientInput D' hi hri hrm data hir di
  j hj hij hs hsm hsn dl hlj hq hq hv dv hv
local notation "outFour" => fourRegimeAmbientLocal D' hi hri hrm data hir di
  j hj hij hir hs hsm hsn dl hlj hsn hq hq hv dv hv
local notation "Quad" => quadrupleAmbientOpen D d
local notation "fquad" => quadrupleAmbientAddition D d

/-- Each chart of the three-regime union agrees with the quadruple ambient law. -/
theorem threeRegimeQuadrupleAmbient_local (b : Option Bool) :
    pullback.fst (incThree b) (Quad).ι ≫ outThree b =
      pullback.snd (incThree b) (Quad).ι ≫ fquad := by
  rcases b with _ | ⟨_ | _⟩
  · exact tripleQuadrupleAmbient_pullback D d D' hq hq
  · exact shallowQuadrupleAmbient_pullback D d D' hs hsm hsn dl hlj hsn
  · exact intermediateQuadrupleAmbient_pullback D d D' hi hri hrm hir di hij hir

/-- The whole three-regime union agrees with the whole quadruple extension. -/
theorem threeRegimeQuadrupleAmbient_pullback :
    pullback.fst (Three).ι (Quad).ι ≫ fthree =
      pullback.snd (Three).ι (Quad).ι ≫ fquad :=
  openImageUnionGlue_single_pullback incThree outThree _ (Quad).ι fquad
    (threeRegimeQuadrupleAmbient_local D d D' hi hri hrm hir di hij hs hsm hsn dl hlj hq)

/-- Both whole charts of the four-regime union agree with the quadruple extension. -/
theorem fourRegimeQuadrupleAmbient_local (b : Bool) :
    pullback.fst (incFour b) (Quad).ι ≫ outFour b =
      pullback.snd (incFour b) (Quad).ι ≫ fquad := by
  cases b
  · exact threeRegimeQuadrupleAmbient_pullback
      D d D' hi hri hrm hir di hij hs hsm hsn dl hlj hq
  · exact deepQuadrupleAmbient_pullback D d D' hv dv hv

/-- The full four-regime and quadruple ambient intersection carries one output. -/
theorem fourRegimeQuadrupleAmbient_pullback :
    pullback.fst (Four).ι (Quad).ι ≫ ffour =
      pullback.snd (Four).ι (Quad).ι ≫ fquad :=
  openImageUnionGlue_single_pullback incFour outFour _ (Quad).ι fquad
    (fourRegimeQuadrupleAmbient_local D d D' hi hri hrm hir di hij
      hs hsm hsn dl hlj hq hv dv)

/-- Every common source in the full four-regime/quadruple intersection has equal outputs. -/
theorem fourRegimeQuadrupleAmbient_overlap {X : Scheme}
    (p : X ⟶ (Four).toScheme) (q : X ⟶ (Quad).toScheme)
    (hpq : p ≫ (Four).ι = q ≫ (Quad).ι) : p ≫ ffour = q ≫ fquad :=
  openImageUnionGlue_single_overlap incFour outFour _ (Quad).ι fquad
    (fourRegimeQuadrupleAmbient_local D d D' hi hri hrm hir di hij
      hs hsm hsn dl hlj hq hv dv) p q hpq

end FLT.Mazur.WeierstrassDividedDepth
