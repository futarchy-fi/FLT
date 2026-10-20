/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiveRegimeAmbientAddition
public import FLT.Mazur.WeierstrassDividedQuadrupleSuppliedAmbient

/-!
# All five ambient laws in a supplied doubled-depth family

Proved uniqueness of the divided coefficients transports the entire glued
law and its two whole constituent extensions to any supplied family.
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
variable (data : (i : Fin (k + k + 1)) → Data W π (0 + i.val))
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
local notation "Four" => fourRegimeAmbientOpen D' hi hri hrm data hir di
  j hj hij hs hsm hsn dl hlj hq hq hv dv hv
local notation "ffour" => fourRegimeAmbientAddition D' hi hri hrm data hir di
  j hj hij hir hs hsm hsn dl hlj hsn hq hq hv dv hv
local notation "Quad" => quadrupleSuppliedAmbientOpen D data d
local notation "fquad" => quadrupleSuppliedAmbientAddition D data d

/-- Transport the entire five-regime domain along proved coefficient uniqueness. -/
def fiveSuppliedAmbientOpen : (finiteResolvedProduct hπ data j hj).Opens := by
  have h := quadrupleSuppliedFamily_eq D data
  subst data
  exact fiveRegimeAmbientOpen D d D' hi hri hrm hir di hij
    hs hsm hsn dl hlj hq hv dv

local notation "Union" => fiveSuppliedAmbientOpen D d data D' hi hri hrm hir di hij
  hs hsm hsn dl hlj hq hv dv

/-- Transport the whole constructed five-regime law. -/
def fiveSuppliedAmbientAddition : (Union).toScheme ⟶ (U).toScheme := by
  have h := quadrupleSuppliedFamily_eq D data
  subst data
  exact fiveRegimeAmbientAddition D d D' hi hri hrm hir di hij
    hs hsm hsn dl hlj hq hv dv

local notation "law" => fiveSuppliedAmbientAddition D d data D' hi hri hrm hir di hij
  hs hsm hsn dl hlj hq hv dv

/-- The domain remains precisely the union of both entire constituent extensions. -/
theorem fiveSuppliedAmbientOpen_eq : Union = Four ⊔ Quad := by
  have h := quadrupleSuppliedFamily_eq D data
  subst data
  exact fiveRegimeAmbientOpen_eq D d D' hi hri hrm hir di hij
    hs hsm hsn dl hlj hq hv dv

/-- The whole four-regime domain maps into the transported union. -/
def fiveSuppliedFourInclusion : (Four).toScheme ⟶ (Union).toScheme := by
  have h := quadrupleSuppliedFamily_eq D data
  subst data
  exact openImageUnionMap (fiveRegimeAmbientInput D d D' hi hri hrm hir di hij
    hs hsm hsn dl hlj hq hv dv) false

/-- The whole supplied quadruple domain maps into the transported union. -/
def fiveSuppliedQuadrupleInclusion : (Quad).toScheme ⟶ (Union).toScheme := by
  have h := quadrupleSuppliedFamily_eq D data
  subst data
  exact openImageUnionMap (fiveRegimeAmbientInput D d D' hi hri hrm hir di hij
    hs hsm hsn dl hlj hq hv dv) true

/-- The inclusion of the four-regime domain is its literal ambient inclusion. -/
@[reassoc] theorem fiveSuppliedFourInclusion_ι :
    fiveSuppliedFourInclusion D d data D' hi hri hrm hir di hij
  hs hsm hsn dl hlj hq hv dv ≫ (Union).ι = (Four).ι := by
  have h := quadrupleSuppliedFamily_eq D data
  subst data
  exact openImageUnionMap_fac (fiveRegimeAmbientInput D d D' hi hri hrm hir di hij
    hs hsm hsn dl hlj hq hv dv) false

/-- The inclusion of the quadruple domain is its literal ambient inclusion. -/
@[reassoc] theorem fiveSuppliedQuadrupleInclusion_ι :
    fiveSuppliedQuadrupleInclusion D d data D' hi hri hrm hir di hij
  hs hsm hsn dl hlj hq hv dv ≫ (Union).ι = (Quad).ι := by
  have h := quadrupleSuppliedFamily_eq D data
  subst data
  exact openImageUnionMap_fac (fiveRegimeAmbientInput D d D' hi hri hrm hir di hij
    hs hsm hsn dl hlj hq hv dv) true

/-- The entire supplied four-regime extension is retained. -/
@[reassoc] theorem fiveSuppliedAmbientAddition_four :
    fiveSuppliedFourInclusion D d data D' hi hri hrm hir di hij
  hs hsm hsn dl hlj hq hv dv ≫ law = ffour := by
  have h := quadrupleSuppliedFamily_eq D data
  subst data
  exact fiveRegimeAmbientAddition_four D d D' hi hri hrm hir di hij
    hs hsm hsn dl hlj hq hv dv

/-- The entire supplied quadruple extension is retained. -/
@[reassoc] theorem fiveSuppliedAmbientAddition_quadruple :
    fiveSuppliedQuadrupleInclusion D d data D' hi hri hrm hir di hij
  hs hsm hsn dl hlj hq hv dv ≫ law = fquad := by
  have h := quadrupleSuppliedFamily_eq D data
  subst data
  exact fiveRegimeAmbientAddition_quadruple D d D' hi hri hrm hir di hij
    hs hsm hsn dl hlj hq hv dv

/-- The transported union law preserves the first input's coefficient point. -/
@[reassoc] theorem fiveSuppliedAmbientAddition_structure :
    law ≫ t = (Union).ι ≫ pullback.fst t t ≫ t := by
  have h := quadrupleSuppliedFamily_eq D data
  subst data
  exact fiveRegimeAmbientAddition_structure D d D' hi hri hrm hir di hij
    hs hsm hsn dl hlj hq hv dv

/-- The same coefficient point is preserved from the second input. -/
@[reassoc] theorem fiveSuppliedAmbientAddition_structure_snd :
    law ≫ t = (Union).ι ≫ pullback.snd t t ≫ t := by
  rw [fiveSuppliedAmbientAddition_structure, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
