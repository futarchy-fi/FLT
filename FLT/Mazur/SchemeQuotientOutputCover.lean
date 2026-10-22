/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemePairSymmetryPoints

/-!
# Whole outputs and changes of domain for open covers

These elementary constructions keep the entire coefficient morphism when
restricting a covered output or exchanging the two inputs of a relative pair.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z S : Scheme.{0}} (t : Z ⟶ S)

/-- A whole output provides a one-chart cover with the same coefficient map. -/
theorem schemeQuotientOutputCover_ofWhole (f : X ⟶ S) (out : X ⟶ Z)
    (h : out ≫ t = f) :
    ∃ (C : X.OpenCover.{0}) (output : (i : C.I₀) → C.X i ⟶ Z),
      ∀ i, output i ≫ t = C.f i ≫ f := by
  refine ⟨Scheme.coverOfIsIso (𝟙 X), fun _ => out, ?_⟩
  intro i
  change out ≫ t = 𝟙 X ≫ f
  rw [Category.id_comp]
  exact h

/-- Pull an actual covered output back along any scheme morphism. -/
theorem schemeQuotientOutputCover_pullback (f : X ⟶ S) (g : Y ⟶ X)
    (C : X.OpenCover.{0}) (out : (i : C.I₀) → C.X i ⟶ Z)
    (h : ∀ i, out i ≫ t = C.f i ≫ f) :
    ∃ (D : Y.OpenCover.{0}) (output : (i : D.I₀) → D.X i ⟶ Z),
      ∀ i, output i ≫ t = D.f i ≫ g ≫ f := by
  refine ⟨C.pullback₁ g, fun i => C.pullbackHom g i ≫ out i, ?_⟩
  intro i
  rw [Category.assoc, h, ← Category.assoc, Scheme.Cover.pullbackHom_map, Category.assoc]

/-- Reversing both inputs carries the whole output and its original coefficient map. -/
theorem schemeQuotientOutputCover_swap (f : X ⟶ S) (g : Y ⟶ S)
    (C : (pullback f g : Scheme).OpenCover.{0}) (out : (i : C.I₀) → C.X i ⟶ Z)
    (h : ∀ i, out i ≫ t = C.f i ≫ pullback.fst f g ≫ f) :
    ∃ (D : (pullback g f : Scheme).OpenCover.{0}) (output : (i : D.I₀) → D.X i ⟶ Z),
      ∀ i, output i ≫ t = D.f i ≫ pullback.fst g f ≫ g := by
  obtain ⟨D, output, he⟩ := schemeQuotientOutputCover_pullback t
    (pullback.fst f g ≫ f) (pullbackSymmetry g f).hom C out h
  refine ⟨D, output, ?_⟩
  intro i
  rw [he, pullbackSymmetry_hom_comp_fst_assoc, ← pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
