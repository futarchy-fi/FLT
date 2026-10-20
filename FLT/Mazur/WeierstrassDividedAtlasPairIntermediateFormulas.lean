/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAtlasPairIntermediateAddition

/-!
# The two actual local formulas on each new atlas-pair addition domain

The tangent and secant source preimages cover precisely the new formula open.
On each preimage the constructed addition recovers the whole promoted output.
This does not assert that the formula open is the whole chart product.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] globalIntegralAtlasObject globalIntegralAtlasMap
  globalSmoothAtlasOpen globalSmoothAtlasMap
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure rootShearCurve
  nodalSecondShear nodalSecondQuotient
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  [IsNoetherianRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n k m r : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 3 * k ≤ m) (hrk : r ≤ k) (hrm : r ≤ m - 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hr : k + r ≤ n)
  (j : ℕ) (hj : j ≤ n) (hrj : k + r ≤ j)
  (a b : Fin (j + 3)) (d : Data W π k)
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "ca" => globalSmoothAtlasMap hπ data j hj a
local notation "cb" => globalSmoothAtlasMap hπ data j hj b
local notation "ta" => ca ≫ t
local notation "tb" => cb ≫ t
local notation "A" => Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R A))
variable (f : globalIntegralAtlasObject data j hj a ⟶ chart d)
  (g : globalIntegralAtlasObject data j hj b ⟶ chart d)
variable
  (hf : f ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (Coordinate W (π ^ k) d.b3 d.b4 d.b6))) =
      globalIntegralAtlasMap D.uniformizer_ne_zero data j hj a ≫
        finiteGlobalStructure D.uniformizer_ne_zero data j hj)
  (hg : g ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (Coordinate W (π ^ k) d.b3 d.b4 d.b6))) =
      globalIntegralAtlasMap D.uniformizer_ne_zero data j hj b ≫
        finiteGlobalStructure D.uniformizer_ne_zero data j hj)
local notation "input" => atlasPairFormulaInput hπ data j hj a b d f g hf hg
local notation "al" => dividedPairLeft W (π ^ k) d.b3 d.b4 d.b6
local notation "ar" => dividedPairRight W (π ^ k) d.b3 d.b4 d.b6
local notation "O" => nodalIntermediateAdditionOpen D hdepth hrk hrm data hr d al ar
local notation "law" => nodalIntermediatePromotedAddition D hdepth hrk hrm data hr d al ar j hj hrj

local notation "inc" => nodalIntermediateAdditionInclusion D hdepth hrk hrm data hr d al ar
local notation "out" => nodalIntermediateAdditionOutput D hdepth hrk hrm data hr d al ar
local notation "C" => Scheme.Opens.iSupOpenCover (fun i => (inc i).opensRange)
local notation "V" => atlasPairIntermediateOpen D hdepth hrk hrm data hr j hj a b d f g hf hg
local notation "add" => atlasPairIntermediateAddition
  D hdepth hrk hrm data hr j hj hrj a b d f g hf hg
local notation "promote" => finiteGlobalSmoothTransition hπ data (k + r) j hrj hj

/-- The preimage of an entire original tangent or secant output domain. -/
def atlasPairIntermediateFormulaOpen (i : Bool) : (pullback ta tb).Opens :=
  input ⁻¹ᵁ (inc i).opensRange

local notation "Vi" => atlasPairIntermediateFormulaOpen
  D hdepth hrk hrm data hr j hj a b d f g hf hg

/-- These two formula opens cover exactly the constructed pair-domain union. -/
theorem atlasPairIntermediateFormulaOpen_union : (⨆ i, Vi i) = V := by
  exact (Scheme.Hom.preimage_iSup input (fun i => (inc i).opensRange)).symm

/-- Either whole formula preimage lies in the constructed addition domain. -/
theorem atlasPairIntermediateFormulaOpen_le (i : Bool) : Vi i ≤ V := by
  rw [← atlasPairIntermediateFormulaOpen_union]
  exact le_iSup Vi i

/-- The inclusion of a local formula domain into the whole constructed pair domain. -/
def atlasPairIntermediateFormulaInclusion (i : Bool) : (Vi i).toScheme ⟶ (V).toScheme :=
  Scheme.homOfLE _ (atlasPairIntermediateFormulaOpen_le
    D hdepth hrk hrm data hr j hj a b d f g hf hg i)

local notation "incl" => atlasPairIntermediateFormulaInclusion
  D hdepth hrk hrm data hr j hj a b d f g hf hg

/-- Restricting common coordinates commutes with either actual formula-domain inclusion. -/
@[reassoc] theorem atlasPairIntermediateFormulaInclusion_coordinates (i : Bool) :
    incl i ≫ (input ∣_ O) = (input ∣_ (inc i).opensRange) ≫ (C).f i := by
  apply (cancel_mono (O).ι).mp
  simp only [Category.assoc, morphismRestrict_ι,
    atlasPairIntermediateFormulaInclusion]
  rw [show (C).f i ≫ (O).ι = (inc i).opensRange.ι from
    Scheme.homOfLE_ι _ (le_iSup (fun i => (inc i).opensRange) i), morphismRestrict_ι]
  exact Scheme.homOfLE_ι_assoc _ (atlasPairIntermediateFormulaOpen_le
    D hdepth hrk hrm data hr j hj a b d f g hf hg i) input

/-- On either whole formula preimage the addition is the actual promoted local output. -/
@[reassoc] theorem atlasPairIntermediateAddition_formula (i : Bool) :
    incl i ≫ add = (input ∣_ (inc i).opensRange) ≫
      (inc i).isoOpensRange.inv ≫ out i ≫ promote := by
  unfold atlasPairIntermediateAddition nodalIntermediatePromotedAddition
  rw [atlasPairIntermediateFormulaInclusion_coordinates_assoc
    D hdepth hrk hrm data hr j hj a b d f g hf hg i,
    nodalIntermediateAddition_restrict_assoc D hdepth hrk hrm data hr d al ar i]
  simp only [nodalIntermediateAdditionLocalOutput, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
