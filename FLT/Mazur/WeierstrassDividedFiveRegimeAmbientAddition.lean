/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourRegimeQuadrupleAmbientOverlap

/-!
# Glue the whole four-regime law and the quadruple ambient extension

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

/-- The two entire ambient source schemes. -/
def fiveRegimeAmbientChart (b : Bool) : Scheme :=
  if b then (Quad).toScheme else (Four).toScheme

/-- Both existing ambient domains embed openly in the same resolved product. -/
def fiveRegimeAmbientInput : (b : Bool) →
    fiveRegimeAmbientChart D d D' hi hri hrm hir di hij
      hs hsm hsn dl hlj hq hv dv b ⟶ finiteResolvedProduct hπ data j hj
  | false => (Four).ι
  | true => (Quad).ι

local notation "inc" => fiveRegimeAmbientInput D d D' hi hri hrm hir di hij
      hs hsm hsn dl hlj hq hv dv

instance fiveRegimeAmbientInput_open (b : Bool) :
    IsOpenImmersion (inc b) := by
  apply Bool.forall_bool.mpr ?_ b
  constructor <;> dsimp only [fiveRegimeAmbientInput] <;> infer_instance

/-- Both constructed ambient laws on their whole existing domains. -/
def fiveRegimeAmbientLocal : (b : Bool) →
    fiveRegimeAmbientChart D d D' hi hri hrm hir di hij
      hs hsm hsn dl hlj hq hv dv b ⟶ (U).toScheme
  | false => ffour
  | true => fquad

local notation "out" => fiveRegimeAmbientLocal D d D' hi hri hrm hir di hij
      hs hsm hsn dl hlj hq hv dv

/-- All pairwise intersections carry the same constructed output. -/
theorem fiveRegimeAmbient_compatible (b b' : Bool) :
    pullback.fst (inc b) (inc b') ≫ out b =
      pullback.snd (inc b) (inc b') ≫ out b' := by
  cases b <;> cases b'
  · exact congrArg (· ≫ ffour) ((cancel_mono (Four).ι).mp pullback.condition)
  · exact fourRegimeQuadrupleAmbient_pullback D d D' hi hri hrm hir di hij
      hs hsm hsn dl hlj hq hv dv
  · exact (fourRegimeQuadrupleAmbient_overlap D d D' hi hri hrm hir di hij
      hs hsm hsn dl hlj hq hv dv _ _ pullback.condition.symm).symm
  · exact congrArg (· ≫ fquad) ((cancel_mono (Quad).ι).mp pullback.condition)

/-- The actual union of the two previous ambient domains. -/
def fiveRegimeAmbientOpen : (finiteResolvedProduct hπ data j hj).Opens :=
  openImageUnion inc

local notation "Union" => fiveRegimeAmbientOpen D d D' hi hri hrm hir di hij
      hs hsm hsn dl hlj hq hv dv

/-- The two actual ambient laws glue on their full union. -/
def fiveRegimeAmbientAddition : (Union).toScheme ⟶ (U).toScheme :=
  openImageUnionGlue inc out (fiveRegimeAmbient_compatible
    D d D' hi hri hrm hir di hij
      hs hsm hsn dl hlj hq hv dv)

local notation "law" => fiveRegimeAmbientAddition D d D' hi hri hrm hir di hij
      hs hsm hsn dl hlj hq hv dv

/-- The entire four-regime ambient extension is preserved. -/
@[reassoc] theorem fiveRegimeAmbientAddition_four :
    openImageUnionMap inc false ≫ law = ffour := openImageUnionGlue_fac _ _ _ false

/-- The entire quadruple ambient extension is preserved. -/
@[reassoc] theorem fiveRegimeAmbientAddition_quadruple :
    openImageUnionMap inc true ≫ law = fquad := openImageUnionGlue_fac _ _ _ true

/-- The domain is exactly the union of both previous ambient opens. -/
theorem fiveRegimeAmbientOpen_eq : Union = Four ⊔ Quad := by
  simp only [fiveRegimeAmbientOpen, openImageUnion, iSup_bool_eq,
    fiveRegimeAmbientInput, Scheme.Opens.opensRange_ι, sup_comm]

/-- The glued law retains the coefficient point of the first input. -/
@[reassoc] theorem fiveRegimeAmbientAddition_structure :
    law ≫ t = (Union).ι ≫ pullback.fst t t ≫ t := by
  apply openImageUnion_hom_ext inc
  intro b
  cases b
  · rw [fiveRegimeAmbientAddition_four_assoc,
      fourRegimeAmbientAddition_structure]
    exact (openImageUnionMap_fac_assoc inc false (pullback.fst t t ≫ t)).symm
  · rw [fiveRegimeAmbientAddition_quadruple_assoc,
      quadrupleAmbientAddition_structure]
    exact (openImageUnionMap_fac_assoc inc true (pullback.fst t t ≫ t)).symm

/-- The same coefficient point is retained from the second input. -/
@[reassoc] theorem fiveRegimeAmbientAddition_structure_snd :
    law ≫ t = (Union).ι ≫ pullback.snd t t ≫ t := by
  rw [fiveRegimeAmbientAddition_structure, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
