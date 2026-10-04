/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedProjChartPullback

/-!
# Gluing the actual section-ring Proj charts

A trivializing open cover with invertible positive-degree global sections
gives a morphism to the Proj of the full section ring. Compatibility on the
actual fibre-product overlaps follows from pullback of generators and the
coordinate- and denominator-independence theorems.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open Scheme.Modules
namespace FLT.Mazur.SectionGradedProjGluing
open FCurve ModuleLineBundleTensorPullback SectionGradedSum SectionGradedProjChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme} (L : X.Modules) [Fact (LocallyFreeRankOne L)]

/-- The two local Proj maps agree after pullback to their actual fibre-product overlap. -/
lemma overlap_maps {Y Z : Scheme} (p : Y ⟶ X) (q : Z ⟶ X)
    (ep : (Scheme.Modules.pullback p).obj L ≅ structureModule Y)
    (eq : (Scheme.Modules.pullback q).obj L ≅ structureModule Z)
    {d n : ℕ} (s : Γ(tensorPower L d, ⊤)) (t : Γ(tensorPower L n, ⊤))
    (hd : 0 < d) (hn : 0 < n)
    (hs : IsUnit (SectionGradedProjChart.ringHom p L ep (of L ⊤ d s)))
    (ht : IsUnit (SectionGradedProjChart.ringHom q L eq (of L ⊤ n t))) :
    pullback.fst p q ≫ toProj p L ep (of L ⊤ d s) hs ⟨s, rfl⟩ hd =
      pullback.snd p q ≫ toProj q L eq (of L ⊤ n t) ht ⟨t, rfl⟩ hn := by
  let k := pullback.fst p q
  let l := pullback.snd p q
  let ei := pullTrivialization p L ep k
  let ej := pullTrivialization q L eq l
  have hi := ringHom_isUnit_pullback p L ep k ei s hs
  have hj := ringHom_isUnit_pullback q L eq l ej t ht
  have hgen : IsIso (globalSectionHom _
      (pullGlobal (k ≫ p) (tensorPower L n) t)) := by
    change IsIso (globalSectionHom _
      (pullGlobal (pullback.fst _ _ ≫ p) (tensorPower L n) t))
    rw [pullback.condition]
    exact pullGenerator_isIso_of_ringHom (l ≫ q) L ej t hj
  have hj' := ringHom_isUnit_of_pullGenerator (k ≫ p) L ei t
  rw [toProj_pullback, toProj_pullback]
  exact (toProj_eq (k ≫ p) L ei _ _ hi hj' _ hd _ hn).trans
    (toProj_congr (k ≫ p) L ei (pullback.condition ..) ej _ hj' hj _ hn)

variable (𝒰 : X.OpenCover)
  (e : ∀ i, (Scheme.Modules.pullback (𝒰.f i)).obj L ≅ structureModule (𝒰.X i))
  (d : 𝒰.I₀ → ℕ) (s : ∀ i, Γ(tensorPower L (d i), ⊤)) (hd : ∀ i, 0 < d i)
  (hs : ∀ i, IsUnit (SectionGradedProjChart.ringHom (𝒰.f i) L (e i) (of L ⊤ (d i) (s i))))

/-- The actual maps to Proj agree on every fibre-product overlap. -/
lemma overlap (i j : 𝒰.I₀) :
    pullback.fst (𝒰.f i) (𝒰.f j) ≫
      toProj (𝒰.f i) L (e i) (of L ⊤ (d i) (s i)) (hs i) ⟨s i, rfl⟩ (hd i) =
    pullback.snd (𝒰.f i) (𝒰.f j) ≫
      toProj (𝒰.f j) L (e j) (of L ⊤ (d j) (s j)) (hs j) ⟨s j, rfl⟩ (hd j) :=
  overlap_maps L (𝒰.f i) (𝒰.f j) (e i) (e j) (s i) (s j) (hd i) (hd j) (hs i) (hs j)

/-- Glue the actual section-ring charts on a trivializing generating open cover. -/
def fromCover : X ⟶ Proj (grade L ⊤) :=
  𝒰.glueMorphisms
    (fun i ↦ toProj (𝒰.f i) L (e i) (of L ⊤ (d i) (s i)) (hs i) ⟨s i, rfl⟩ (hd i))
    (overlap L 𝒰 e d s hd hs)

/-- The glued morphism restricts to the constructed Proj map on each chart. -/
@[reassoc]
lemma fromCover_chart (i : 𝒰.I₀) :
    𝒰.f i ≫ fromCover L 𝒰 e d s hd hs =
      toProj (𝒰.f i) L (e i) (of L ⊤ (d i) (s i)) (hs i) ⟨s i, rfl⟩ (hd i) :=
  𝒰.ι_glueMorphisms _ _ i

/-- The glued morphism is independent of all choices of trivializing generating cover. -/
lemma fromCover_independent (𝒱 : X.OpenCover)
    (e' : ∀ i, (Scheme.Modules.pullback (𝒱.f i)).obj L ≅ structureModule (𝒱.X i))
    (d' : 𝒱.I₀ → ℕ) (s' : ∀ i, Γ(tensorPower L (d' i), ⊤)) (hd' : ∀ i, 0 < d' i)
    (hs' : ∀ i, IsUnit (SectionGradedProjChart.ringHom
      (𝒱.f i) L (e' i) (of L ⊤ (d' i) (s' i)))) :
    fromCover L 𝒰 e d s hd hs = fromCover L 𝒱 e' d' s' hd' hs' := by
  apply 𝒰.hom_ext
  intro i
  apply Scheme.Cover.hom_ext (𝒱.pullback₁ (𝒰.f i))
  intro j
  change pullback.fst (𝒰.f i) (𝒱.f j) ≫ (𝒰.f i ≫ _) =
    pullback.fst (𝒰.f i) (𝒱.f j) ≫ (𝒰.f i ≫ _)
  conv_rhs => rw [← Category.assoc, pullback.condition, Category.assoc]
  rw [fromCover_chart, fromCover_chart]
  exact overlap_maps L (𝒰.f i) (𝒱.f j) (e i) (e' j) (s i) (s' j)
    (hd i) (hd' j) (hs i) (hs' j)

/-- The glued map has the specified chart formula after any further pullback. -/
@[reassoc]
lemma fromCover_comp {Y : Scheme} (p : Y ⟶ X)
    (ep : (Scheme.Modules.pullback p).obj L ≅ structureModule Y)
    {n : ℕ} (t : Γ(tensorPower L n, ⊤)) (hn : 0 < n)
    (ht : IsUnit (SectionGradedProjChart.ringHom p L ep (of L ⊤ n t))) :
    p ≫ fromCover L 𝒰 e d s hd hs = toProj p L ep (of L ⊤ n t) ht ⟨t, rfl⟩ hn := by
  apply Scheme.Cover.hom_ext (𝒰.pullback₁ p)
  intro i
  change pullback.fst p (𝒰.f i) ≫ (p ≫ _) = pullback.fst p (𝒰.f i) ≫ _
  conv_lhs => rw [← Category.assoc, pullback.condition, Category.assoc, fromCover_chart]
  exact (overlap_maps L p (𝒰.f i) ep (e i) t (s i) hn (hd i) ht (hs i)).symm

end FLT.Mazur.SectionGradedProjGluing
