/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkingSpecialization

/-!
# Scheme points over power series are determined by their finite restrictions

An affine neighborhood of the common closed image contains both entire maps,
since the base is local. Completeness in affine coordinates then proves equality.
The target need not be separated or affine.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] {X : Scheme}

/-- A neighborhood of the closed image contains the entire image of a local-base point. -/
theorem powerSeriesPoint_range_subset (f : Spec (.of (PowerSeries K)) ⟶ X)
    (U : X.Opens) (hf : f (closedPoint (PowerSeries K)) ∈ U) :
    Set.range f ⊆ (U : Set X) := by
  rintro _ ⟨x, rfl⟩
  exact ((specializes_closedPoint x).map f.continuous).mem_open U.isOpen hf

/-- Actual scheme points over power series agree if all their finite restrictions agree. -/
theorem powerSeriesPoint_ext {f g : Spec (.of (PowerSeries K)) ⟶ X}
    (hfg : ∀ m, baseToSeries K m ≫ f = baseToSeries K m ≫ g) : f = g := by
  have hc : f (closedPoint (PowerSeries K)) = g (closedPoint (PowerSeries K)) := by
    rw [← baseToSeries_stageBasePoint K 0]
    exact congrArg (fun k : Spec (.of (Ring K 0)) ⟶ X ↦ k (stageBasePoint K 0)) (hfg 0)
  obtain ⟨U, hU, hfU, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := f (closedPoint (PowerSeries K))) trivial
  have hgU : g (closedPoint (PowerSeries K)) ∈ U := hc ▸ hfU
  have hf : Set.range f ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact powerSeriesPoint_range_subset K f U hfU
  have hg : Set.range g ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact powerSeriesPoint_range_subset K g U hgU
  let f' := IsOpenImmersion.lift hU.fromSpec f hf
  let g' := IsOpenImmersion.lift hU.fromSpec g hg
  have hff : f' ≫ hU.fromSpec = f := IsOpenImmersion.lift_fac _ _ _
  have hgg : g' ≫ hU.fromSpec = g := IsOpenImmersion.lift_fac _ _ _
  have he : f' = g' := by
    apply affinePoint_ext K Γ(X, U)
    intro m
    apply (cancel_mono hU.fromSpec).mp
    rw [Category.assoc, Category.assoc, hff, hgg, hfg]
  rw [← hff, ← hgg, he]

/-- Reconstruction from compatible stages is independent of the chosen affine chart. -/
theorem pointFromAffineStages_unique
    (s : baseSystem K ⟶ (Functor.const ℕ).obj X)
    (U : X.Opens) (hU : IsAffineOpen U)
    (hs : ∀ m, Set.range (s.app m) ⊆ (U : Set X))
    (f : Spec (.of (PowerSeries K)) ⟶ X)
    (hf : ∀ m, baseToSeries K m ≫ f = s.app m) :
    f = pointFromAffineStages K s U hU hs := by
  apply powerSeriesPoint_ext K
  intro m
  rw [hf, baseToSeries_pointFromAffineStages]

/-- Reconstruction commutes with any target morphism respecting the specified stage maps. -/
@[reassoc] theorem pointFromAffineStages_naturality
    {Y : Scheme} (s : baseSystem K ⟶ (Functor.const ℕ).obj X)
    (t : baseSystem K ⟶ (Functor.const ℕ).obj Y)
    (U : X.Opens) (hU : IsAffineOpen U)
    (hs : ∀ m, Set.range (s.app m) ⊆ (U : Set X))
    (V : Y.Opens) (hV : IsAffineOpen V)
    (ht : ∀ m, Set.range (t.app m) ⊆ (V : Set Y))
    (f : X ⟶ Y) (hf : ∀ m, s.app m ≫ f = t.app m) :
    pointFromAffineStages K s U hU hs ≫ f = pointFromAffineStages K t V hV ht := by
  apply powerSeriesPoint_ext K
  intro m
  rw [← Category.assoc, baseToSeries_pointFromAffineStages,
    baseToSeries_pointFromAffineStages, hf]

end FLT.Mazur.PolygonInfinitesimalStages
