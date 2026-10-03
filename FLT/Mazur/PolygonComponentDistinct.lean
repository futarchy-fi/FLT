/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonComponentImages
/-!
# Distinct polygon components

Disjoint Laurent opens have distinct closures. Together with component
classification this gives an equivalence with Fin n.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.PolygonComponentDistinct
open PolygonPinching
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
include h in
theorem torus_disjoint {i j : Fin n} (hij : i ≠ j) :
    Disjoint (Set.range (torusToComponent K ≫ componentι K n i ≫ p).left)
      (Set.range (torusToComponent K ≫ componentι K n j ≫ p).left) := by
  rw [← torus_polygonIso K n hn p q h i, ← torus_polygonIso K n hn p q h j]
  have : IsIso (polygonIso K n hn p q h).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (polygonIso K n hn p q h).hom))
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, he⟩
  have he' : (PolygonAtlas.torus K n j).left y = (PolygonAtlas.torus K n i).left x :=
    (polygonIso K n hn p q h).hom.left.isOpenEmbedding.injective he
  exact Set.disjoint_left.mp (PolygonAtlas.disjoint_torus K n hij) ⟨x, rfl⟩ ⟨y, he'⟩
include h in
theorem injective : Function.Injective
    (fun i : Fin n ↦ Set.range (componentι K n i ≫ p).left) := by
  intro i j he
  dsimp only at he
  by_contra hij
  have hd := torus_disjoint K n hn p q h hij
  have := torus_isOpenImmersion K n hn p q h j
  have hc := hd.closure_left
    (torusToComponent K ≫ componentι K n j ≫ p).left.isOpenEmbedding.isOpenMap.isOpen_range
  rw [PolygonComponentImages.closure_torus K n hn p q h i, he,
    ← PolygonComponentImages.closure_torus K n hn p q h j] at hc
  have : Nonempty (MultiplicativeGroupScheme.gm K).left :=
    inferInstanceAs (Nonempty (ProjectiveLine.overlap K))
  obtain ⟨x, hx⟩ := Set.range_nonempty (torusToComponent K ≫ componentι K n j ≫ p).left
  exact Set.disjoint_left.mp hc (subset_closure hx) hx
/-- The actual irreducible components, indexed by the specified normalization. -/
def equivalence : Fin n ≃ irreducibleComponents C.left :=
  Equiv.ofBijective (fun i ↦ ⟨Set.range (componentι K n i ≫ p).left,
    PolygonComponentImages.mem_components K n hn p q h i⟩)
    ⟨fun _ _ he ↦ injective K n hn p q h (congrArg Subtype.val he), by
      rintro ⟨Z, hZ⟩
      rw [PolygonComponentImages.components_eq K n hn p q h] at hZ
      obtain ⟨i, rfl⟩ := hZ
      exact ⟨i, rfl⟩⟩
end FLT.Mazur.PolygonComponentDistinct
