/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenIrreducibleComponent
public import FLT.Mazur.ProjectiveLineTopology
public import FLT.Mazur.PolygonProper
public import FLT.Mazur.PolygonSmoothLocus
/-!
# Irreducible components of polygon pinching cocones

Proper normalization images are the closures of the specified Laurent opens.
These closures are irreducible components and cover the polygon.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.PolygonComponentImages
open PolygonPinching
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
include h in
theorem component_proper (i : Fin n) : IsProper (componentι K n i ≫ p).left := by
  have := PolygonSeparated.cocone K n hn p q h
  have : IsProper ((componentι K n i ≫ p).left ≫ C.hom) := by
    rw [Over.w]
    exact PolygonProper.projectiveLine K
  exact IsProper.of_comp _ C.hom
include h in
theorem closure_torus (i : Fin n) :
    closure (Set.range (torusToComponent K ≫ componentι K n i ≫ p).left) =
      Set.range (componentι K n i ≫ p).left := by
  have := component_proper K n hn p q h i
  have he : ((torusToComponent K ≫ componentι K n i ≫ p).left : _ → C.left) =
      (componentι K n i ≫ p).left ∘ (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) := by
    ext x
    exact Scheme.Hom.comp_apply _ _ _
  rw [he, Set.range_comp, ((componentι K n i ≫ p).left.isClosedMap).closure_image_eq_of_continuous
    (componentι K n i ≫ p).left.continuous,
    (ProjectiveLineTopology.torus_dense K).closure_range, Set.image_univ]
include h in
theorem cover (x : C.left) : ∃ i y, (componentι K n i ≫ p).left y = x := by
  obtain ⟨z, rfl⟩ := PolygonNormalizationFinite.cocone_normalization_surjective K n hn p q h x
  let e := asIso (sigmaComparison (Over.forget (Spec (.of K)))
    (fun _ : Fin n ↦ component K))
  obtain ⟨w, rfl⟩ := e.hom.homeomorph.surjective z
  obtain ⟨i, y, rfl⟩ := (sigmaOpenCover (fun _ : Fin n ↦ ProjectiveLine.scheme K)).exists_eq w
  change Fin n at i
  change ProjectiveLine.scheme K at y
  refine ⟨i, y, ?_⟩
  have he : Sigma.ι (fun _ : Fin n ↦ ProjectiveLine.scheme K) i ≫ e.hom =
      (componentι K n i).left :=
    ι_comp_sigmaComparison (Over.forget (Spec (.of K))) (fun _ : Fin n ↦ component K) i
  change (componentι K n i ≫ p).left y =
    p.left (e.hom (Sigma.ι (fun _ : Fin n ↦ ProjectiveLine.scheme K) i y))
  change ((componentι K n i).left ≫ p.left) y = _
  rw [Scheme.Hom.comp_apply]
  have hh := congrArg (fun f ↦ p.left (f y)) he
  convert hh.symm using 1
  rfl
include h in
theorem mem_components (i : Fin n) :
    Set.range (componentι K n i ≫ p).left ∈ irreducibleComponents C.left := by
  rw [← closure_torus K n hn p q h i]
  have := torus_isOpenImmersion K n hn p q h i
  apply OpenIrreducibleComponent.closure_mem
    (torusToComponent K ≫ componentι K n i ≫ p).left.isOpenEmbedding.isOpenMap.isOpen_range
  have hi := (IrreducibleSpace.isIrreducible_univ (ProjectiveLine.overlap K)).image
    (torusToComponent K ≫ componentι K n i ≫ p).left
    (torusToComponent K ≫ componentι K n i ≫ p).left.continuous.continuousOn
  simpa only [Set.image_univ] using hi
include h in
theorem components_eq : irreducibleComponents C.left =
    Set.range (fun i : Fin n ↦ Set.range (componentι K n i ≫ p).left) := by
  classical
  apply Set.Subset.antisymm
  · intro Z hZ
    let S : Finset (Set C.left) := Finset.univ.image
      (fun i : Fin n ↦ Set.range (componentι K n i ≫ p).left)
    obtain ⟨V, hV, hZV⟩ := isIrreducible_iff_sUnion_isClosed.mp hZ.1 S (by
      intro V hV
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hV
      exact isClosed_of_mem_irreducibleComponents _ (mem_components K n hn p q h i)) (by
      intro x _
      obtain ⟨i, y, rfl⟩ := cover K n hn p q h x
      exact Set.mem_sUnion.mpr ⟨_, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, y, rfl⟩)
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hV
    exact ⟨i, Set.Subset.antisymm
      (hZ.2 (mem_components K n hn p q h i).1 hZV) hZV⟩
  · rintro _ ⟨i, rfl⟩
    exact mem_components K n hn p q h i
end FLT.Mazur.PolygonComponentImages
