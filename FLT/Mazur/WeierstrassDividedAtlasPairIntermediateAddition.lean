/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAtlasPairFormulaInput
public import FLT.Mazur.WeierstrassDividedNodalIntermediatePromotedAddition

/-!
# Intermediate addition on actual resolved chart-pair formula domains

Pull back the constructed universal tangent/secant law along common divided
coordinates. Only the original resolved chart inputs are restricted to be
smooth; their contracted divided inputs need not be smooth.
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

/-- The actual formula domain inside the full relative product of the two smooth charts. -/
def atlasPairIntermediateOpen : (pullback ta tb).Opens := input ⁻¹ᵁ O

local notation "V" => atlasPairIntermediateOpen D hdepth hrk hrm data hr j hj a b d f g hf hg

/-- The constructed tangent/secant output on this genuine atlas-pair domain. -/
def atlasPairIntermediateAddition : (V).toScheme ⟶ (U).toScheme := (input ∣_ O) ≫ law

local notation "add" => atlasPairIntermediateAddition
  D hdepth hrk hrm data hr j hj hrj a b d f g hf hg

/-- The entire formula domain embeds openly into the complete resolved product. -/
def atlasPairIntermediateInput : (V).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b

instance atlasPairIntermediateInput_open :
    IsOpenImmersion
      (atlasPairIntermediateInput D hdepth hrk hrm data hr j hj a b d f g hf hg) := by
  unfold atlasPairIntermediateInput
  infer_instance

/-- Both actual inputs and the constructed output have the same coefficient point. -/
@[reassoc] theorem atlasPairIntermediateAddition_structure :
    add ≫ t = atlasPairIntermediateInput D hdepth hrk hrm data hr j hj a b d f g hf hg ≫
      pullback.fst t t ≫ t := by
  rw [atlasPairIntermediateAddition, Category.assoc,
    nodalIntermediatePromotedAddition_structure, morphismRestrict_ι_assoc,
    atlasPairFormulaInput_structure]
  rfl

/-- The second actual input retains the same coefficient point as the output. -/
@[reassoc] theorem atlasPairIntermediateAddition_structure_snd :
    add ≫ t = atlasPairIntermediateInput D hdepth hrk hrm data hr j hj a b d f g hf hg ≫
      pullback.snd t t ≫ t := by
  rw [atlasPairIntermediateAddition_structure, pullback.condition]

/-- Membership is exactly membership of the contracted pair in the constructed formula union. -/
theorem atlasPairIntermediateOpen_mem
    (z : (finiteResolvedPairCover D.uniformizer_ne_zero data j hj).X (a, b)) :
    z ∈ V ↔ input z ∈ O := Iff.rfl

/-- Restriction keeps the whole universal intermediate output after its actual stage promotion. -/
@[reassoc] theorem atlasPairIntermediateAddition_contraction :
    add ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (input ∣_ O) ≫ nodalIntermediateAddition D hdepth hrk hrm data hr d al ar ≫
        (finiteGlobalStructure hπ data (k + r) hr).smoothLocus.ι ≫
          finiteGlobalContraction hπ data (k + r) hr := by
  rw [atlasPairIntermediateAddition, Category.assoc,
    nodalIntermediatePromotedAddition_contraction]

end FLT.Mazur.WeierstrassDividedDepth
