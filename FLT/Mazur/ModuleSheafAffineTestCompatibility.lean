/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafRefinementGluing
public import FLT.Mazur.SheafPullbackMapNormalization

/-!
# Open gluing compatibility detected by affine tests

Affine covers of the actual source intersections detect compatibility of
normalized pullback maps. The intersections themselves need not be affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u v
namespace FLT.Mazur.ModuleSheafOpenImmersionGluing
open SheafPullbackMapNormalization SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} {M N : X.Modules} {ι : Type v}
variable (Y : ι → Scheme.{u}) (i : ∀ j, Y j ⟶ X) [∀ j, IsOpenImmersion (i j)]
variable (a : ∀ j, (pullback (i j)).obj M ⟶ (pullback (i j)).obj N)

/-- Agreement on affine tests of source intersections gives actual gluing compatibility. -/
lemma compatible_of_affine_tests
    (h : ∀ j k {A : CommRingCat.{u}} (l : Spec A ⟶ Y j) (r : Spec A ⟶ Y k)
      (d : Spec A ⟶ X) (hl : l ≫ i j = d) (hr : r ≫ i k = d),
      normalize l (i j) (i j) d d hl hl (a j) =
        normalize r (i k) (i k) d d hr hr (a k)) : Compatible Y i a := by
  let U (j k : ι) := (Limits.pullback (i j) (i k)).affineOpenCover
  let l (j k : ι) (q : (U j k).I₀) := (U j k).f q ≫ Limits.pullback.fst (i j) (i k)
  let r (j k : ι) (q : (U j k).I₀) := (U j k).f q ≫ Limits.pullback.snd (i j) (i k)
  let d (j k : ι) (q : (U j k).I₀) := l j k q ≫ i j
  have hr (j k : ι) (q : (U j k).I₀) : r j k q ≫ i k = d j k q := by
    simp only [r, d, l, Category.assoc, Limits.pullback.condition]
  refine compatible_of_geometric_refinements Y i a
    (fun j k ↦ (U j k).I₀) (fun j k q ↦ Spec ((U j k).X q)) d l r
    (fun _ _ _ ↦ rfl) hr ?_
    (fun j k q ↦ normalize (l j k q) (i j) (i j) (d j k q) (d j k q) rfl rfl (a j)) ?_ ?_
  · intro j k x hx
    have hx' : x ∈ Set.range (Limits.pullback.fst (i j) (i k) ≫ i j) := by
      rw [IsOpenImmersion.range_pullback_to_base_of_left]
      exact hx
    obtain ⟨z, rfl⟩ := hx'
    obtain ⟨q, y, hy⟩ : ∃ q, z ∈ Set.range ((U j k).f q) :=
      ⟨(U j k).idx z, (U j k).covers z⟩
    refine ⟨q, y, ?_⟩
    change (Limits.pullback.fst (i j) (i k) ≫ i j) ((U j k).f q y) = _
    rw [hy]
  · intro j k q
    exact (normalize_comm (l j k q) (i j) (i j) (d j k q) (d j k q)
      rfl rfl (a j)).symm
  · intro j k q
    rw [h j k (l j k q) (r j k q) (d j k q) rfl (hr j k q)]
    exact (normalize_comm (r j k q) (i k) (i k) (d j k q) (d j k q)
      (hr j k q) (hr j k q) (a k)).symm

end FLT.Mazur.ModuleSheafOpenImmersionGluing
