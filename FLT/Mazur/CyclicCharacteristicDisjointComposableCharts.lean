/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointComparisonArrows
public import FLT.Mazur.SchemeCoproductPullbackDecomposition

/-!
# Component charts of the global composable-arrow scheme

Matching middle components recover the actual ordered-pair fiber products.
Mismatching middle components have empty fiber products.
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

/-- The actual fiber product of the assembled target and source maps. -/
def disjointComposableScheme : Scheme := pullback tgt src

/-- A chart retains both ordered-pair components of a composable pair. -/
abbrev disjointComposableChart (p : (Bool × Bool) × (Bool × Bool)) : Scheme :=
  SchemeCoproductPullback.chart X X tgt src p

/-- The global composable scheme decomposes by its actual component charts. -/
def disjointComposableDecomposition :
    (∐ disjointComposableChart n) ≅ disjointComposableScheme n :=
  SchemeCoproductPullback.decompositionIso X X tgt src

/-- The two middle base maps agree in the assembled normalized source. -/
theorem disjointComposableChart_middle (p : (Bool × Bool) × (Bool × Bool)) :
    (pullback.fst _ _ : disjointComposableChart n p ⟶ _) ≫
        productArrowTarget n p.1.1 p.1.2 ≫ normalizedDisjointInclusion n p.1.2 =
      pullback.snd _ _ ≫ productArrowSource n p.2.1 p.2.2 ≫
        normalizedDisjointInclusion n p.2.1 := by
  have h := pullback.condition (f := disjointComparisonInclusion n p.1.1 p.1.2 ≫ tgt)
    (g := disjointComparisonInclusion n p.2.1 p.2.2 ≫ src)
  simpa only [disjointComparisonInclusion_target, disjointComparisonInclusion_source,
    Category.assoc] using! h

/-- Incompatible middle components give an empty composable chart. -/
theorem disjointComposableChart_empty (p : (Bool × Bool) × (Bool × Bool))
    (h : p.1.2 ≠ p.2.1) : IsEmpty (disjointComposableChart n p) := by
  apply isEmpty_of_commSq_sigmaι_of_ne (g := normalizedLocus n) (i := p.1.2) (j := p.2.1)
    (a := pullback.fst _ _ ≫ productArrowTarget n p.1.1 p.1.2)
    (b := pullback.snd _ _ ≫ productArrowSource n p.2.1 p.2.2) _ h
  exact ⟨by simpa only [Category.assoc] using! disjointComposableChart_middle n p⟩

/-- On matching middle components, cancel the open inclusion to recover composability. -/
def disjointComposableChartToProduct (b c d : Bool) :
    disjointComposableChart n ((b, c), (c, d)) ⟶ productComposableScheme n b c d :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _)
    ((cancel_mono (normalizedDisjointInclusion n c)).mp
      (by simpa only [Category.assoc] using disjointComposableChart_middle n ((b, c), (c, d))))

/-- The recovered composable pair retains its first comparison. -/
@[reassoc] theorem disjointComposableChartToProduct_first (b c d : Bool) :
    disjointComposableChartToProduct n b c d ≫ productComposableFirst n b c d =
      pullback.fst _ _ := pullback.lift_fst _ _ _

/-- The recovered composable pair retains its second comparison. -/
@[reassoc] theorem disjointComposableChartToProduct_second (b c d : Bool) :
    disjointComposableChartToProduct n b c d ≫ productComposableSecond n b c d =
      pullback.snd _ _ := pullback.lift_snd _ _ _

/-- Composition on every chart uses the actual ordered-pair composition morphism. -/
def disjointCompositionOnChart (p : (Bool × Bool) × (Bool × Bool)) :
    disjointComposableChart n p ⟶ disjointComparisonArrows n := by
  obtain ⟨⟨b, c⟩, ⟨d, e⟩⟩ := p
  by_cases h : c = d
  · subst d
    exact disjointComposableChartToProduct n b c e ≫ productCompositionMap n b c e ≫
      disjointComparisonInclusion n b e
  · let _ := disjointComposableChart_empty n ((b, c), (d, e)) h
    exact isInitialOfIsEmpty.to _

/-- Matching chart composition is exactly the constructed ordered-pair composition. -/
theorem disjointCompositionOnChart_matching (b c d : Bool) :
    disjointCompositionOnChart n ((b, c), (c, d)) =
      disjointComposableChartToProduct n b c d ≫ productCompositionMap n b c d ≫
        disjointComparisonInclusion n b d := by
  simp [disjointCompositionOnChart]

end FLT.Mazur.CyclicCharacteristicAtlas
