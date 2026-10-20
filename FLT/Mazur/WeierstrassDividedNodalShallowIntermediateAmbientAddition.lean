/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalShallowIntermediateAmbientOverlap

/-!
# Glue both cross-depth ambient extensions

The actual shallow and intermediate ambient opens carry a single law on their
union. Both entire prior extensions, and their coefficient maps, are retained.
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

variable {l : ℕ} (hs : 2 * l ≤ m) (hsm : m ≤ 3 * l)
  (hsn : m - 2 * l ≤ n) (d' : Data W π l)
  (hlj : l ≤ j) (hsj : m - 2 * l ≤ j)
local notation "a'" => dividedPairLeft W (π ^ l) d'.b3 d'.b4 d'.b6
local notation "c'" => dividedPairRight W (π ^ l) d'.b3 d'.b4 d'.b6
local notation "left" => nodalShallowAmbientInput D hs hsm data hsn d' j hj hlj
local notation "right" => nodalIntermediateAmbientInput D hdepth hrk hrm data hr d j hj hkj
local notation "L" => nodalShallowAmbientOpen D hs hsm data hsn d' j hj hlj
local notation "N" => nodalIntermediateAmbientOpen D hdepth hrk hrm data hr d j hj hkj
local notation "fl" => nodalShallowAmbientAddition D hs hsm data hsn d' j hj hlj hsj
local notation "fr" => nodalIntermediateAmbientAddition D hdepth hrk hrm data hr d j hj hkj hrj

/-- The two entire ambient source schemes. -/
def nodalShallowIntermediateAmbientChart (b : Bool) : Scheme :=
  if b then (N).toScheme else (L).toScheme

/-- Both existing ambient domains embed openly in the same resolved product. -/
def nodalShallowIntermediateAmbientInput : (b : Bool) →
    nodalShallowIntermediateAmbientChart D hdepth hrk hrm data hr d j hj hkj
      hs hsm hsn d' hlj b ⟶ finiteResolvedProduct hπ data j hj
  | false => (L).ι
  | true => (N).ι

local notation "inc" => nodalShallowIntermediateAmbientInput D hdepth hrk hrm data hr d
  j hj hkj hs hsm hsn d' hlj

instance nodalShallowIntermediateAmbientInput_open (b : Bool) :
    IsOpenImmersion (inc b) := by
  apply Bool.forall_bool.mpr ?_ b
  constructor <;> dsimp only [nodalShallowIntermediateAmbientInput] <;> infer_instance

/-- Both constructed ambient laws on their whole existing domains. -/
def nodalShallowIntermediateAmbientLocal : (b : Bool) →
    nodalShallowIntermediateAmbientChart D hdepth hrk hrm data hr d j hj hkj
      hs hsm hsn d' hlj b ⟶ (U).toScheme
  | false => fl
  | true => fr

local notation "out" => nodalShallowIntermediateAmbientLocal D hdepth hrk hrm data hr d
  j hj hkj hrj hs hsm hsn d' hlj hsj

/-- All pairwise intersections carry the same constructed output. -/
theorem nodalShallowIntermediateAmbient_compatible (b b' : Bool) :
    pullback.fst (inc b) (inc b') ≫ out b =
      pullback.snd (inc b) (inc b') ≫ out b' := by
  cases b <;> cases b'
  · exact congrArg (· ≫ fl) ((cancel_mono (L).ι).mp pullback.condition)
  · exact nodalShallowIntermediateAmbient_pullback D hdepth hrk hrm data hr d j hj hkj hrj
      hs hsm hsn d' hlj hsj
  · exact (nodalShallowIntermediateAmbient_overlap D hdepth hrk hrm data hr d j hj hkj hrj
      hs hsm hsn d' hlj hsj _ _ pullback.condition.symm).symm
  · exact congrArg (· ≫ fr) ((cancel_mono (N).ι).mp pullback.condition)

/-- The actual union of the two previous ambient domains. -/
def nodalShallowIntermediateAmbientOpen : (finiteResolvedProduct hπ data j hj).Opens :=
  openImageUnion inc

local notation "Union" => nodalShallowIntermediateAmbientOpen D hdepth hrk hrm data hr d
  j hj hkj hs hsm hsn d' hlj

/-- The two actual ambient laws glue on their full union. -/
def nodalShallowIntermediateAmbientAddition : (Union).toScheme ⟶ (U).toScheme :=
  openImageUnionGlue inc out (nodalShallowIntermediateAmbient_compatible
    D hdepth hrk hrm data hr d j hj hkj hrj hs hsm hsn d' hlj hsj)

local notation "law" => nodalShallowIntermediateAmbientAddition D hdepth hrk hrm data hr d
  j hj hkj hrj hs hsm hsn d' hlj hsj

/-- The entire shallow ambient extension is preserved. -/
@[reassoc] theorem nodalShallowIntermediateAmbientAddition_shallow :
    openImageUnionMap inc false ≫ law = fl := openImageUnionGlue_fac _ _ _ false

/-- The entire intermediate ambient extension is preserved. -/
@[reassoc] theorem nodalShallowIntermediateAmbientAddition_intermediate :
    openImageUnionMap inc true ≫ law = fr := openImageUnionGlue_fac _ _ _ true

/-- The domain is exactly the union of both previous ambient opens. -/
theorem nodalShallowIntermediateAmbientOpen_eq : Union = L ⊔ N := by
  simp only [nodalShallowIntermediateAmbientOpen, openImageUnion, iSup_bool_eq,
    nodalShallowIntermediateAmbientInput, Scheme.Opens.opensRange_ι, sup_comm]

/-- The glued law retains the coefficient point of the first input. -/
@[reassoc] theorem nodalShallowIntermediateAmbientAddition_structure :
    law ≫ t = (Union).ι ≫ pullback.fst t t ≫ t := by
  apply openImageUnion_hom_ext inc
  intro b
  cases b
  · rw [nodalShallowIntermediateAmbientAddition_shallow_assoc,
      nodalShallowAmbientAddition_structure]
    exact (openImageUnionMap_fac_assoc inc false (pullback.fst t t ≫ t)).symm
  · rw [nodalShallowIntermediateAmbientAddition_intermediate_assoc,
      nodalIntermediateAmbientAddition_structure]
    exact (openImageUnionMap_fac_assoc inc true (pullback.fst t t ≫ t)).symm

/-- The same coefficient point is retained from the second input. -/
@[reassoc] theorem nodalShallowIntermediateAmbientAddition_structure_snd :
    law ≫ t = (Union).ι ≫ pullback.snd t t ≫ t := by
  rw [nodalShallowIntermediateAmbientAddition_structure, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
