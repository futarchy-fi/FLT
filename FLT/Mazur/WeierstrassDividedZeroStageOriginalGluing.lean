/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticZeroStageAction
public import FLT.Mazur.WeierstrassDividedAtlasOriginalActionOverlap

/-!
# Glue the complete stage-zero resolved smooth addition

All nine actual chart pairs carry the original action. Their full overlap
equalities glue to one morphism on the entire resolved smooth product.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
local notation "hj" => Nat.zero_le n
local notation "base" => finiteGlobalStructure hπ data 0 hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "O" => finiteResolvedAtlasOpen hπ data 0 hj
local notation "toPair" => finiteResolvedAtlasOpenToPair hπ data 0 hj
local notation "input" => finiteResolvedAtlasPairInput hπ data 0 hj
local notation "out" => atlasOriginalActionOutput hπ data 0 hj
local notation "cover" => finiteResolvedAtlasCover hπ data 0 hj

/-- The actual output on each of the nine open domains of the full product. -/
def zeroStageOriginalChartOutput (ab : Fin 3 × Fin 3) :
    (O ab.1 ab.2).toScheme ⟶ (U).toScheme := toPair ab.1 ab.2 ≫ out ab.1 ab.2

local notation "law" => zeroStageOriginalChartOutput hπ data

/-- Every common refinement of two whole chart domains has the same resolved output. -/
theorem zeroStageOriginalChartOutput_common (ab cd : Fin 3 × Fin 3) {X : Scheme}
    (f : X ⟶ (O ab.1 ab.2).toScheme) (g : X ⟶ (O cd.1 cd.2).toScheme)
    (h : f ≫ (O ab.1 ab.2).ι = g ≫ (O cd.1 cd.2).ι) :
    f ≫ law ab = g ≫ law cd := by
  unfold zeroStageOriginalChartOutput
  rw [← Category.assoc f, ← Category.assoc g]
  apply atlasOriginalActionOutput_common
  simpa only [Category.assoc, finiteResolvedAtlasOpenToPair_input] using h

/-- Glue the full stage-zero law across the actual complete product cover. -/
def zeroStageOriginalAddition : finiteResolvedProduct hπ data 0 hj ⟶ (U).toScheme :=
  (cover).glueMorphisms law (fun ab cd =>
    zeroStageOriginalChartOutput_common hπ data ab cd _ _ pullback.condition)

local notation "add" => zeroStageOriginalAddition hπ data

/-- Every complete chart formula is retained by the glued output. -/
@[reassoc] theorem zeroStageOriginalAddition_chart (ab : Fin 3 × Fin 3) :
    (O ab.1 ab.2).ι ≫ add = law ab := (cover).ι_glueMorphisms _ _ ab

/-- The glued law restricts to the whole original chart-pair action morphism. -/
@[reassoc] theorem zeroStageOriginalAddition_pair (a b : Fin 3) :
    input a b ≫ add = out a b := by
  apply (cancel_epi (finiteResolvedAtlasPairIso hπ data 0 hj a b).hom).mp
  change toPair a b ≫ (input a b ≫ add) = toPair a b ≫ out a b
  rw [finiteResolvedAtlasOpenToPair_input_assoc]
  exact zeroStageOriginalAddition_chart hπ data (a, b)

/-- The glued law preserves the entire first coefficient morphism. -/
@[reassoc] theorem zeroStageOriginalAddition_structure :
    add ≫ t = pullback.fst t t ≫ t := by
  apply (cover).hom_ext
  intro ab
  change (O ab.1 ab.2).ι ≫ _ = (O ab.1 ab.2).ι ≫ _
  rw [zeroStageOriginalAddition_chart_assoc, zeroStageOriginalChartOutput,
    Category.assoc, atlasOriginalActionOutput_structure]
  rw [← finiteResolvedAtlasPairInput_fst_assoc,
    finiteResolvedAtlasOpenToPair_input_assoc]

/-- The second full input has the same unchanged coefficient morphism. -/
@[reassoc] theorem zeroStageOriginalAddition_structure_snd :
    add ≫ t = pullback.snd t t ≫ t := by
  rw [zeroStageOriginalAddition_structure, pullback.condition]

/-- The nine complete local action formulas uniquely determine the glued morphism. -/
theorem zeroStageOriginalAddition_unique (f : finiteResolvedProduct hπ data 0 hj ⟶ (U).toScheme)
    (hf : ∀ a b, input a b ≫ f = out a b) : f = add := by
  apply (cover).hom_ext
  intro ab
  change (O ab.1 ab.2).ι ≫ f = (O ab.1 ab.2).ι ≫ add
  rw [zeroStageOriginalAddition_chart]
  rw [← finiteResolvedAtlasOpenToPair_input hπ data 0 hj ab.1 ab.2,
    Category.assoc, hf]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
