/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBranchDifferenceSheaf

/-!
# Cartesian node charts of the cyclic polygon

A node lies in exactly its own cyclic chart, since overlaps are punctured
branches. The resulting cartesian square uses the specified node coproduct.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.CyclicNodeChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open PolygonNodePresentation PolygonCyclicAtlas
variable (K : Type u) [Field K] (n : ℕ) (hn : 2 ≤ n)
/-- The nodes of the cyclic atlas, initially formed as a scheme coproduct. -/
def nodeMap : (∐ fun _ : Fin n ↦ Spec (.of K)) ⟶ scheme K n hn :=
  Sigma.desc fun i ↦ aOrigin K ≫ chart K n hn i

theorem origin_not_left (x : Spec (.of K)) :
    aOrigin K x ∉ Set.range (PolygonNodeBranches.left K) := by
  intro hx
  have hz : aOrigin K x ∈ Set.range (aOrigin K) := ⟨x, rfl⟩
  have he := PolygonNodeBranches.branches_cover_complement K
  rw [a_zeroLocus_origin] at he
  have hnot : aOrigin K x ∈ (Set.range (aOrigin K))ᶜ := by
    rw [← he]
    exact Or.inl hx
  exact hnot hz

theorem origin_not_right (x : Spec (.of K)) :
    aOrigin K x ∉ Set.range (PolygonNodeBranches.right K) := by
  intro hx
  have hz : aOrigin K x ∈ Set.range (aOrigin K) := ⟨x, rfl⟩
  have he := PolygonNodeBranches.branches_cover_complement K
  rw [a_zeroLocus_origin] at he
  have hnot : aOrigin K x ∈ (Set.range (aOrigin K))ᶜ := by
    rw [← he]
    exact Or.inr hx
  exact hnot hz

theorem origin_chart_index (i j : Fin n) (x : Spec (.of K))
    (y : PolygonNodeBranches.node K) (he : chart K n hn i (aOrigin K x) = chart K n hn j y) :
    i = j := by
  by_contra hij
  rcases (charts_eq_iff K n hn hij _ _).mp he with
    ⟨z, _, hz, _⟩ | ⟨z, _, hz, _⟩
  · exact origin_not_left K x ⟨z, hz⟩
  · exact origin_not_right K x ⟨(ProjectiveLine.inversion K).hom z, hz⟩

theorem preimage_chart (j : Fin n) :
    nodeMap K n hn ⁻¹ᵁ (chart K n hn j).opensRange =
      (Sigma.ι (fun _ : Fin n ↦ Spec (.of K)) j).opensRange := by
  ext x
  obtain ⟨i, x, rfl⟩ := (sigmaOpenCover (fun _ : Fin n ↦ Spec (.of K))).exists_eq x
  change nodeMap K n hn (Sigma.ι (fun _ : Fin n ↦ Spec (.of K)) i x) ∈
      Set.range (chart K n hn j) ↔
    Sigma.ι (fun _ : Fin n ↦ Spec (.of K)) i x ∈
      Set.range (Sigma.ι (fun _ : Fin n ↦ Spec (.of K)) j)
  rw [← Scheme.Hom.comp_apply, nodeMap, Sigma.ι_comp_desc]
  constructor
  · rintro ⟨y, hy⟩
    have hij := origin_chart_index K n hn i j x y hy.symm
    subst j
    exact ⟨x, rfl⟩
  · rintro ⟨y, hy⟩
    have hij := congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : Fin n ↦ Spec (.of K))
      j i y x).mp hy)
    change j = i at hij
    subst j
    exact ⟨aOrigin K x, rfl⟩

theorem isPullback (j : Fin n) :
    IsPullback (aOrigin K) (Sigma.ι (fun _ : Fin n ↦ Spec (.of K)) j)
      (chart K n hn j) (nodeMap K n hn) := by
  apply IsOpenImmersion.isPullback _ _ _ _ _ (preimage_chart K n hn j)
  simp [nodeMap]
/-- The canonical passage from the scheme coproduct to the specified node coproduct. -/
abbrev comparison := sigmaComparison (Over.forget (Spec (.of K)))
  (fun _ : Fin n ↦ PolygonPinching.point K)
@[reassoc] theorem comparison_nodes :
    comparison K n ≫ (nodes K n hn).left = nodeMap K n hn := by
  apply Sigma.hom_ext
  intro i
  rw [ι_comp_sigmaComparison_assoc]
  change (PolygonPinching.nodeι K n i ≫ nodes K n hn).left = _
  rw [nodeι_nodes]
  simp [nodeMap]
instance nodeι_open (i : Fin n) : IsOpenImmersion (PolygonPinching.nodeι K n i).left := by
  have he : Sigma.ι (fun _ : Fin n ↦ Spec (.of K)) i ≫ comparison K n =
      (PolygonPinching.nodeι K n i).left :=
    ι_comp_sigmaComparison (Over.forget (Spec (.of K)))
      (fun _ : Fin n ↦ PolygonPinching.point K) i
  rw [← he]
  infer_instance

theorem specified_isPullback (j : Fin n) :
    IsPullback (aOrigin K) (PolygonPinching.nodeι K n j).left
      (chart K n hn j) (nodes K n hn).left := by
  apply (isPullback K n hn j).of_iso (Iso.refl _) (Iso.refl _)
    (asIso (comparison K n)) (Iso.refl _)
  · simp
  · dsimp only [Iso.refl_hom, asIso_hom]
    rw [Category.id_comp]
    exact ι_comp_sigmaComparison (Over.forget (Spec (.of K)))
      (fun _ : Fin n ↦ PolygonPinching.point K) j
  · simp
  · simpa only [Iso.refl_hom, asIso_hom, Category.comp_id] using (comparison_nodes K n hn).symm
end FLT.Mazur.CyclicNodeChart
