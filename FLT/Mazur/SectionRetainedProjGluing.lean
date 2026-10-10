/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionRetainedProjChart

/-!
# Gluing retained section-ring Proj charts

The retained charts agree on actual fiber-product overlaps. Gluing them
constructs a morphism from the original scheme and retains the original
chart formula after every pullback carrying an invertible retained section.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Scheme.Modules

namespace FLT.Mazur.SectionRetainedProjGluing

open FCurve ModuleLineBundleTensorPullback SectionGradedSum SectionRetainedProjChart
open SectionRetainedChartComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} (L : X.Modules) [Fact (LocallyFreeRankOne L)]
  (q : ℕ) [GradedRing (RetainedSubringGrading.grade (grade L ⊤) q)]

/-- Retained Proj charts agree on their original fiber-product overlap. -/
theorem overlap_maps {Y Z : Scheme} (p : Y ⟶ X) (r : Z ⟶ X)
    (ep : (Scheme.Modules.pullback p).obj L ≅ structureModule Y)
    (er : (Scheme.Modules.pullback r).obj L ≅ structureModule Z)
    {d n : ℕ} (s : Γ(tensorPower L (q * d), ⊤)) (t : Γ(tensorPower L (q * n), ⊤))
    (hd : 0 < d) (hn : 0 < n)
    (hs : IsUnit (SectionGradedProjChart.ringHom p L ep (of L ⊤ (q * d) s)))
    (ht : IsUnit (SectionGradedProjChart.ringHom r L er (of L ⊤ (q * n) t))) :
    pullback.fst p r ≫ toProj p L ep q (insertion L q d s) hs (insertion_mem L q d s) hd =
    pullback.snd p r ≫ toProj r L er q (insertion L q n t) ht (insertion_mem L q n t) hn := by
  let k := pullback.fst p r
  let l := pullback.snd p r
  let ei := SectionGradedProjChart.pullTrivialization p L ep k
  let ej := SectionGradedProjChart.pullTrivialization r L er l
  have hi := SectionGradedProjChart.ringHom_isUnit_pullback p L ep k ei s hs
  have hj := SectionGradedProjChart.ringHom_isUnit_pullback r L er l ej t ht
  have hgen : IsIso (globalSectionHom _
      (pullGlobal (k ≫ p) (tensorPower L (q * n)) t)) := by
    change IsIso (globalSectionHom _
      (pullGlobal (pullback.fst _ _ ≫ p) (tensorPower L (q * n)) t))
    rw [pullback.condition]
    exact SectionGradedProjChart.pullGenerator_isIso_of_ringHom (l ≫ r) L ej t hj
  have hj' := SectionGradedProjChart.ringHom_isUnit_of_pullGenerator (k ≫ p) L ei t
  rw [toProj_pullback, toProj_pullback]
  exact (toProj_eq (k ≫ p) L ei q _ _ hi hj' _ hd _ hn).trans
    (toProj_congr (k ≫ p) L ei q (pullback.condition ..) ej _ hj' hj _ hn)

variable (𝒰 : X.OpenCover)
  (e : ∀ i, (Scheme.Modules.pullback (𝒰.f i)).obj L ≅ structureModule (𝒰.X i))
  (d : 𝒰.I₀ → ℕ) (s : ∀ i, Γ(tensorPower L (q * d i), ⊤)) (hd : ∀ i, 0 < d i)
  (hs : ∀ i, IsUnit (SectionGradedProjChart.ringHom
    (𝒰.f i) L (e i) (of L ⊤ (q * d i) (s i))))

/-- The original trivializing cover glues retained Proj charts to a scheme morphism. -/
def fromCover : X ⟶ Proj (RetainedSubringGrading.grade (grade L ⊤) q) :=
  𝒰.glueMorphisms
    (fun i ↦ toProj (𝒰.f i) L (e i) q (insertion L q (d i) (s i)) (hs i)
      (insertion_mem L q (d i) (s i)) (hd i))
    (fun i j ↦ overlap_maps L q (𝒰.f i) (𝒰.f j) (e i) (e j)
      (s i) (s j) (hd i) (hd j) (hs i) (hs j))

/-- Gluing retains the original local section evaluation on every chart. -/
@[reassoc]
theorem fromCover_chart (i : 𝒰.I₀) :
    𝒰.f i ≫ fromCover L q 𝒰 e d s hd hs =
      toProj (𝒰.f i) L (e i) q (insertion L q (d i) (s i)) (hs i)
        (insertion_mem L q (d i) (s i)) (hd i) :=
  𝒰.ι_glueMorphisms _ _ i

/-- The glued morphism retains the local chart formula after any further pullback. -/
@[reassoc]
theorem fromCover_comp {Y : Scheme} (p : Y ⟶ X)
    (ep : (Scheme.Modules.pullback p).obj L ≅ structureModule Y)
    {n : ℕ} (t : Γ(tensorPower L (q * n), ⊤)) (hn : 0 < n)
    (ht : IsUnit (SectionGradedProjChart.ringHom p L ep (of L ⊤ (q * n) t))) :
    p ≫ fromCover L q 𝒰 e d s hd hs =
      toProj p L ep q (insertion L q n t) ht (insertion_mem L q n t) hn := by
  apply Scheme.Cover.hom_ext (𝒰.pullback₁ p)
  intro i
  change pullback.fst p (𝒰.f i) ≫ (p ≫ _) = pullback.fst p (𝒰.f i) ≫ _
  conv_lhs => rw [← Category.assoc, pullback.condition, Category.assoc, fromCover_chart]
  exact (overlap_maps L q p (𝒰.f i) ep (e i) t (s i) hn (hd i) ht (hs i)).symm

/-- The retained Proj morphism is independent of the chosen trivializing generating cover. -/
theorem fromCover_independent (𝒱 : X.OpenCover)
    (e' : ∀ i, (Scheme.Modules.pullback (𝒱.f i)).obj L ≅ structureModule (𝒱.X i))
    (d' : 𝒱.I₀ → ℕ) (s' : ∀ i, Γ(tensorPower L (q * d' i), ⊤)) (hd' : ∀ i, 0 < d' i)
    (hs' : ∀ i, IsUnit (SectionGradedProjChart.ringHom
      (𝒱.f i) L (e' i) (of L ⊤ (q * d' i) (s' i)))) :
    fromCover L q 𝒰 e d s hd hs = fromCover L q 𝒱 e' d' s' hd' hs' := by
  apply 𝒰.hom_ext
  intro i
  rw [fromCover_chart, fromCover_comp L q 𝒱 e' d' s' hd' hs']

end FLT.Mazur.SectionRetainedProjGluing
