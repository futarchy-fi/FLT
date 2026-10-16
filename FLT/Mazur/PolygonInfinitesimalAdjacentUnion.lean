/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonInfinitesimalAtlas
public import FLT.Mazur.SchemeOpenPushoutCoverIso

/-!
# Adjacent full nodes as actual polygon open unions

For distinct labels with only one intervening cyclic edge, the standard
puncture pushout embeds into the polygon and is exactly their open union.
The reverse-edge exclusion deliberately retains the exceptional two-gon.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.PolygonInfinitesimal
open PolygonSmoothing
universe u
variable (R : Type u) [CommRing R] (t : R) [Fact (IsNilpotent t)]
  (n : ℕ) (h : 2 ≤ n) (i j : Fin n)
  (hij : (finRotate n).symm i = j) (hne : i ≠ j)
  (hji : (finRotate n).symm j ≠ i)
local notation "l" => leftBranchOpen R t
local notation "r" => precedingBranch R t
local notation "c" => chart R t n h

/-- The full adjacent-node pushout maps by the actual polygon inclusions. -/
def adjacentToPolygon : pushout l r ⟶ scheme R t n h :=
  pushout.desc (c i) (c j) (by rw [overlap, hij])

@[reassoc (attr := simp)] theorem adjacentToPolygon_left :
    pushout.inl l r ≫ adjacentToPolygon R t n h i j hij = c i :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)] theorem adjacentToPolygon_right :
    pushout.inr l r ≫ adjacentToPolygon R t n h i j hij = c j :=
  pushout.inr_desc _ _ _

include hne hji in
/-- No extra point identifications occur in a one-edge adjacent pair. -/
theorem adjacentToPolygon_injective :
    Function.Injective (adjacentToPolygon R t n h i j hij) := by
  have he (x y : PolygonSmoothing.chart R t) (heq : c i x = c j y) :
      pushout.inl l r x = pushout.inr l r y := by
    rcases (charts_eq_iff R t n h hne x y).mp heq with ⟨z, _, hx, hy⟩ | ⟨_, hz, _⟩
    · exact (SchemeOpenPushout.inl_eq_inr_iff l r x y).mpr ⟨z, hx, hy⟩
    · exact (hji hz).elim
  intro x y hxy
  rcases SchemeOpenPushout.charts_cover l r x with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases SchemeOpenPushout.charts_cover l r y with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · simp only [← Scheme.Hom.comp_apply, adjacentToPolygon_left] at hxy
    exact congrArg _ ((c i).isOpenEmbedding.injective hxy)
  · simp only [← Scheme.Hom.comp_apply, adjacentToPolygon_left,
      adjacentToPolygon_right] at hxy
    exact he a b hxy
  · simp only [← Scheme.Hom.comp_apply, adjacentToPolygon_left,
      adjacentToPolygon_right] at hxy
    exact (he b a hxy.symm).symm
  · simp only [← Scheme.Hom.comp_apply, adjacentToPolygon_right] at hxy
    exact congrArg _ ((c j).isOpenEmbedding.injective hxy)

include hne hji in
/-- This pushout is an open subscheme of the polygon. -/
theorem adjacentToPolygon_isOpenImmersion :
    IsOpenImmersion (adjacentToPolygon R t n h i j hij) := by
  apply IsOpenImmersion.of_forall_source_exists _
    (adjacentToPolygon_injective R t n h i j hij hne hji)
  intro x
  rcases SchemeOpenPushout.charts_cover l r x with ⟨a, ha⟩ | ⟨a, ha⟩
  · refine ⟨_, pushout.inl l r, inferInstance, ⟨a, ha⟩, ?_⟩
    rw [adjacentToPolygon_left]
    infer_instance
  · refine ⟨_, pushout.inr l r, inferInstance, ⟨a, ha⟩, ?_⟩
    rw [adjacentToPolygon_right]
    infer_instance

/-- Its image is the union of the two full node images. -/
theorem adjacentToPolygon_range :
    Set.range (adjacentToPolygon R t n h i j hij) = Set.range (c i) ∪ Set.range (c j) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rcases SchemeOpenPushout.charts_cover l r x with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact Or.inl ⟨a, (congrArg (fun f ↦ f a)
        (adjacentToPolygon_left R t n h i j hij)).symm⟩
    · exact Or.inr ⟨a, (congrArg (fun f ↦ f a)
        (adjacentToPolygon_right R t n h i j hij)).symm⟩
  · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact ⟨pushout.inl l r a, congrArg (fun f ↦ f a)
        (adjacentToPolygon_left R t n h i j hij)⟩
    · exact ⟨pushout.inr l r a, congrArg (fun f ↦ f a)
        (adjacentToPolygon_right R t n h i j hij)⟩

/-- The standard adjacent pushout identifies the specified polygon open union. -/
def adjacentUnionIso : pushout l r ≅ ((c i).opensRange ⊔ (c j).opensRange).toScheme := by
  let _ := adjacentToPolygon_isOpenImmersion R t n h i j hij hne hji
  exact IsOpenImmersion.isoOfRangeEq (adjacentToPolygon R t n h i j hij)
    ((c i).opensRange ⊔ (c j).opensRange).ι (by
      rw [Scheme.Opens.range_ι, adjacentToPolygon_range]
      rfl)

/-- The union identification preserves its actual inclusion into the polygon. -/
@[reassoc] theorem adjacentUnionIso_polygon :
    (adjacentUnionIso R t n h i j hij hne hji).hom ≫
      ((c i).opensRange ⊔ (c j).opensRange).ι = adjacentToPolygon R t n h i j hij :=
  by
    let _ := adjacentToPolygon_isOpenImmersion R t n h i j hij hne hji
    unfold adjacentUnionIso
    exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end FLT.Mazur.PolygonInfinitesimal
