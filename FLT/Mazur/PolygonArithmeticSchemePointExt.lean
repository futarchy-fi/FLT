/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticMarkingSpecialization

/-!
# Scheme points over the complete arithmetic base are determined by their finite restrictions

An affine neighborhood of the common closed image contains both entire maps,
since the base is local. Completeness in affine coordinates then proves equality.
The target need not be separated or affine.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false

variable (A : Type) [CommRing A] [IsLocalRing A] (π : A)
  (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] {X : Scheme}

/-- A neighborhood of the closed image contains the entire image of a local-base point. -/
theorem arithmeticPoint_range_subset (f : Spec (.of A) ⟶ X)
    (U : X.Opens) (hf : f (closedPoint A) ∈ U) :
    Set.range f ⊆ (U : Set X) := by
  rintro _ ⟨x, rfl⟩
  exact ((specializes_closedPoint x).map f.continuous).mem_open U.isOpen hf

include hgen

/-- Finite arithmetic restrictions detect equality of actual complete-base scheme points. -/
theorem arithmeticPoint_ext {f g : Spec (.of A) ⟶ X}
    (hfg : ∀ m, baseToIntegral A π m ≫ f = baseToIntegral A π m ≫ g) : f = g := by
  have hc : f (closedPoint A) = g (closedPoint A) := by
    rw [← baseToIntegral_stageBasePoint A π hgen 0]
    exact congrArg (fun k : Spec (.of (Quotient A π 0)) ⟶ X ↦ k (stageBasePoint A π hgen 0)) (hfg 0)
  obtain ⟨U, hU, hfU, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := f (closedPoint A)) trivial
  have hgU : g (closedPoint A) ∈ U := hc ▸ hfU
  have hf : Set.range f ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact arithmeticPoint_range_subset A f U hfU
  have hg : Set.range g ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact arithmeticPoint_range_subset A g U hgU
  let f' := IsOpenImmersion.lift hU.fromSpec f hf
  let g' := IsOpenImmersion.lift hU.fromSpec g hg
  have hff : f' ≫ hU.fromSpec = f := IsOpenImmersion.lift_fac _ _ _
  have hgg : g' ≫ hU.fromSpec = g := IsOpenImmersion.lift_fac _ _ _
  have he : f' = g' := by
    apply affinePoint_ext A π Γ(X, U)
    intro m
    apply (cancel_mono hU.fromSpec).mp
    rw [Category.assoc, Category.assoc, hff, hgg, hfg]
  rw [← hff, ← hgg, he]

/-- Reconstruction from compatible stages is independent of the chosen affine chart. -/
theorem pointFromAffineStages_unique
    (s : baseSystem A π ⟶ (Functor.const ℕ).obj X)
    (U : X.Opens) (hU : IsAffineOpen U)
    (hs : ∀ m, Set.range (s.app m) ⊆ (U : Set X))
    (f : Spec (.of A) ⟶ X)
    (hf : ∀ m, baseToIntegral A π m ≫ f = s.app m) :
    f = pointFromAffineStages A π s U hU hs := by
  apply arithmeticPoint_ext A π hgen
  intro m
  rw [hf, baseToIntegral_pointFromAffineStages]

/-- Reconstruction commutes with any target morphism respecting the specified stage maps. -/
@[reassoc] theorem pointFromAffineStages_naturality
    {Y : Scheme} (s : baseSystem A π ⟶ (Functor.const ℕ).obj X)
    (t : baseSystem A π ⟶ (Functor.const ℕ).obj Y)
    (U : X.Opens) (hU : IsAffineOpen U)
    (hs : ∀ m, Set.range (s.app m) ⊆ (U : Set X))
    (V : Y.Opens) (hV : IsAffineOpen V)
    (ht : ∀ m, Set.range (t.app m) ⊆ (V : Set Y))
    (f : X ⟶ Y) (hf : ∀ m, s.app m ≫ f = t.app m) :
    pointFromAffineStages A π s U hU hs ≫ f = pointFromAffineStages A π t V hV ht := by
  apply arithmeticPoint_ext A π hgen
  intro m
  rw [← Category.assoc, baseToIntegral_pointFromAffineStages,
    baseToIntegral_pointFromAffineStages, hf]

end FLT.Mazur.PolygonArithmeticStages
