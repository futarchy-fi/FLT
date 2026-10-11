/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Unions of actual relative open immersions

The union is an open subscheme of the original ambient scheme. Its cover
uses the original source schemes, retaining all relative structure maps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOpenUnion
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {T : Over S} {ι : Type} {U : ι → Over S}
  (a : ∀ i, U i ⟶ T) [∀ i, IsOpenImmersion (a i).left]

/-- The union of the actual image opens in the original ambient scheme. -/
def domain : T.left.Opens := ⨆ i, (a i).left.opensRange

/-- The open union with its unchanged relative structure map. -/
def test : Over S := Over.mk ((domain a).ι ≫ T.hom)

/-- The open union's inclusion into its original ambient test. -/
def inclusion : test a ⟶ T := Over.homMk (domain a).ι

instance inclusion_isOpenImmersion : IsOpenImmersion (inclusion a).left :=
  inferInstanceAs (IsOpenImmersion (domain a).ι)

instance inclusion_mono : Mono (inclusion a) := Over.mono_of_mono_left _

/-- Every original member factors through the constructed union. -/
def chart (i : ι) : U i ⟶ test a := by
  let h : Set.range (a i).left ⊆ Set.range (domain a).ι := by
    rw [Scheme.Opens.range_ι]
    exact le_iSup (fun j ↦ (a j).left.opensRange) i
  let k := IsOpenImmersion.lift (domain a).ι (a i).left h
  exact Over.homMk k (by
    change k ≫ (domain a).ι ≫ T.hom = _
    rw [← Category.assoc, IsOpenImmersion.lift_fac, Over.w])

@[reassoc (attr := simp)]
theorem chart_inclusion (i : ι) : chart a i ≫ inclusion a = a i :=
  Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)

instance chart_isOpenImmersion (i : ι) : IsOpenImmersion (chart a i).left := by
  have : IsOpenImmersion ((chart a i).left ≫ (inclusion a).left) := by
    rw [← Over.comp_left, chart_inclusion]
    infer_instance
  exact IsOpenImmersion.of_comp _ (inclusion a).left

/-- The original members actually cover the union. -/
theorem charts_cover (x : (test a).left) :
    ∃ i, ∃ y : (U i).left, (chart a i).left y = x := by
  obtain ⟨i, y, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp x.property
  refine ⟨i, y, (inclusion a).left.isOpenEmbedding.injective ?_⟩
  change ((chart a i).left ≫ (inclusion a).left) y = _
  rw [← Over.comp_left, chart_inclusion]
  exact hy

/-- The scheme-theoretic open cover by the original source schemes. -/
def cover : (test a).left.OpenCover where
  I₀ := ι
  X i := (U i).left
  f i := (chart a i).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨charts_cover a, fun i ↦ inferInstance⟩

end FLT.Mazur.RelativeOpenUnion
