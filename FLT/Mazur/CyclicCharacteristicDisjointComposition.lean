/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointComposableCharts

/-!
# Composition on the assembled arrow scheme

The component compositions give an actual morphism on the global fiber product
of target and source. Its restrictions and endpoints are the original ones.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]
local notation "X" => (fun p : Bool × Bool ↦ productSubgroupScheme n (Prod.fst p) (Prod.snd p))
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n
local notation "j" => SchemeCoproductPullback.chartMap X X tgt src

/-- The composition morphism on the actual global composable-arrow fiber product. -/
def disjointCompositionMap : disjointComposableScheme n ⟶ disjointComparisonArrows n :=
  (disjointComposableDecomposition n).inv ≫ Sigma.desc (disjointCompositionOnChart n)

/-- The global composition retains the specified composition on every component chart. -/
@[reassoc] theorem disjointCompositionMap_chart (p : (Bool × Bool) × (Bool × Bool)) :
    j p ≫ disjointCompositionMap n = disjointCompositionOnChart n p := by
  rw [← SchemeCoproductPullback.decompositionIso_inclusion X X tgt src p]
  change (Sigma.ι _ p ≫ (disjointComposableDecomposition n).hom) ≫
    ((disjointComposableDecomposition n).inv ≫ _) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc, Sigma.ι_comp_desc]

/-- Chartwise composition retains the first source, including empty mismatched charts. -/
theorem disjointCompositionOnChart_source (p : (Bool × Bool) × (Bool × Bool)) :
    disjointCompositionOnChart n p ≫ src =
      (pullback.fst _ _ : disjointComposableChart n p ⟶ _) ≫
        disjointComparisonInclusion n p.1.1 p.1.2 ≫ src := by
  obtain ⟨⟨b, c⟩, ⟨d, e⟩⟩ := p
  by_cases h : c = d
  · subst d
    rw [disjointCompositionOnChart_matching]
    simp only [Category.assoc, disjointComparisonInclusion_source,
      productCompositionMap_source_assoc, disjointComposableChartToProduct_first_assoc]
  · let _ := disjointComposableChart_empty n ((b, c), (d, e)) h
    exact isInitialOfIsEmpty.hom_ext _ _

/-- Chartwise composition retains the second target. -/
theorem disjointCompositionOnChart_target (p : (Bool × Bool) × (Bool × Bool)) :
    disjointCompositionOnChart n p ≫ tgt =
      (pullback.snd _ _ : disjointComposableChart n p ⟶ _) ≫
        disjointComparisonInclusion n p.2.1 p.2.2 ≫ tgt := by
  obtain ⟨⟨b, c⟩, ⟨d, e⟩⟩ := p
  by_cases h : c = d
  · subst d
    rw [disjointCompositionOnChart_matching]
    simp only [Category.assoc, disjointComparisonInclusion_target,
      productCompositionMap_target_assoc, disjointComposableChartToProduct_second_assoc]
  · let _ := disjointComposableChart_empty n ((b, c), (d, e)) h
    exact isInitialOfIsEmpty.hom_ext _ _

/-- Global composition retains the source of the first arrow. -/
@[reassoc] theorem disjointCompositionMap_source :
    disjointCompositionMap n ≫ src = pullback.fst tgt src ≫ src := by
  apply (SchemeCoproductPullback.cover X X tgt src).hom_ext
  intro p
  change j p ≫ _ = j p ≫ _
  rw [disjointCompositionMap_chart_assoc, SchemeCoproductPullback.chartMap_fst_assoc]
  exact disjointCompositionOnChart_source n p

/-- Global composition retains the target of the second arrow. -/
@[reassoc] theorem disjointCompositionMap_target :
    disjointCompositionMap n ≫ tgt = pullback.snd tgt src ≫ tgt := by
  apply (SchemeCoproductPullback.cover X X tgt src).hom_ext
  intro p
  change j p ≫ _ = j p ≫ _
  rw [disjointCompositionMap_chart_assoc, SchemeCoproductPullback.chartMap_snd_assoc]
  exact disjointCompositionOnChart_target n p

end FLT.Mazur.CyclicCharacteristicAtlas
