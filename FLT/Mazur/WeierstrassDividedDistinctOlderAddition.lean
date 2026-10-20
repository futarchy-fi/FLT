/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedOlderCoordinates
public import FLT.Mazur.WeierstrassDividedAtlasPairIntermediateAddition

/-!
# Intermediate addition for any two retained older charts

The two creation depths may differ. Contract both entire integral charts to
a common earlier depth, then construct the intermediate formula domain and
output on their actual full smooth relative product. Swapping the depths
supplies the opposite input order. Formula coverage is not asserted here.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  retainedOlderLowerCoordinates retainedOlderFormulaIndex
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  [IsNoetherianRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n k m r : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 3 * (0 + k) ≤ m) (hrk : r ≤ 0 + k) (hrm : r ≤ m - 3 * (0 + k))
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (j : ℕ) (hj : j ≤ n) (hrj : 0 + k + r ≤ j)
  (l₁ l₂ : ℕ) (h₁ : l₁ < j) (h₂ : l₂ < j) (hk₁ : k ≤ l₁) (hk₂ : k ≤ l₂)
local notation "hπ" => D.uniformizer_ne_zero
local notation "a" => retainedOlderFormulaIndex j l₁ h₁
local notation "b" => retainedOlderFormulaIndex j l₂ h₂
local notation "d" => data ⟨k, by omega⟩
local notation "f" => retainedOlderLowerCoordinates hπ data j hj l₁ h₁ k hk₁
local notation "g" => retainedOlderLowerCoordinates hπ data j hj l₂ h₂ k hk₂
local notation "hf" => retainedOlderLowerCoordinates_structure hπ data j hj l₁ h₁ k hk₁
local notation "hg" => retainedOlderLowerCoordinates_structure hπ data j hj l₂ h₂ k hk₂
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "ta" => globalSmoothAtlasMap hπ data j hj a ≫ t
local notation "tb" => globalSmoothAtlasMap hπ data j hj b ≫ t

/-- Explicit tangent/secant domain on the full product of two arbitrary older charts. -/
def distinctOlderIntermediateOpen : (pullback ta tb).Opens :=
  atlasPairIntermediateOpen D hdepth hrk hrm data (hrj.trans hj) j hj a b d f g hf hg

local notation "V" => distinctOlderIntermediateOpen
  D hdepth hrk hrm data j hj hrj l₁ l₂ h₁ h₂ hk₁ hk₂

/-- Construct the output in the chosen final resolved smooth locus. -/
def distinctOlderIntermediateAddition : (V).toScheme ⟶ (U).toScheme :=
  atlasPairIntermediateAddition D hdepth hrk hrm data (hrj.trans hj) j hj hrj
    a b d f g hf hg

local notation "add" => distinctOlderIntermediateAddition
  D hdepth hrk hrm data j hj hrj l₁ l₂ h₁ h₂ hk₁ hk₂

/-- The formula domain is an actual open of the complete resolved input product. -/
def distinctOlderIntermediateInput : (V).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b

instance distinctOlderIntermediateInput_open :
    IsOpenImmersion (distinctOlderIntermediateInput
      D hdepth hrk hrm data j hj hrj l₁ l₂ h₁ h₂ hk₁ hk₂) := by
  unfold distinctOlderIntermediateInput
  infer_instance

/-- The constructed output retains the coefficient point of the first actual input. -/
@[reassoc] theorem distinctOlderIntermediateAddition_structure :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫
      pullback.fst t t ≫ t := by
  unfold distinctOlderIntermediateAddition atlasPairIntermediateAddition
  rw [Category.assoc, nodalIntermediatePromotedAddition_structure,
    morphismRestrict_ι_assoc, atlasPairFormulaInput_structure]
  rfl

/-- The second older input has exactly the same coefficient point as the output. -/
@[reassoc] theorem distinctOlderIntermediateAddition_structure_snd :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫
      pullback.snd t t ≫ t := by
  rw [distinctOlderIntermediateAddition_structure, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
