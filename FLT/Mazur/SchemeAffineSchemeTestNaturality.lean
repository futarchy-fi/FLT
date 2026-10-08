/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineSchemeTestCocycle
public import FLT.Mazur.SchemeAffineTestNaturality

/-!
# Naturality of the actual glued comparisons on scheme tests

An affine open cover detects the naturality square. Normalizing each
restriction reduces the square to effective affine-test naturality.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y W : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {M N : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable (E : SchemeGeometricDescent.Data p N)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
variable [((pullback C.cover).obj N).IsQuasicoherent]
variable [((pullback C'.cover).obj N).IsQuasicoherent]
attribute [local irreducible] sheaf map schemeTestComparison affineTestComparison

/-- The actual glued test comparison is natural for every compatible original map. -/
@[reassoc]
theorem schemeTestComparison_naturality
    (i : W ⟶ Spec C.baseRing) (j : W ⟶ Spec C'.baseRing)
    (w : i ≫ C.base = j ≫ C'.base) (f : M ⟶ N) (hf : D.MapCompatible p E f) :
    (pullback i).map (C.map D E f hf) ≫ C.schemeTestComparison C' E i j w =
      C.schemeTestComparison C' D i j w ≫ (pullback j).map (C'.map D E f hf) := by
  apply ModuleSheafOpenImmersionGluing.hom_ext
    (fun k ↦ Spec (W.affineOpenCover.X k)) W.affineOpenCover.f
    (fun x ↦ ⟨W.affineOpenCover.idx x, W.affineOpenCover.covers x⟩)
  intro k
  let t := W.affineOpenCover.f k
  apply (cancel_mono ((pullbackComp t j).hom.app (C'.sheaf E))).mp
  have hi := (pullbackComp t i).hom.naturality (C.map D E f hf)
  have hj := (pullbackComp t j).hom.naturality (C'.map D E f hf)
  dsimp only [Functor.comp_map] at hi hj
  simp only [Functor.map_comp, Category.assoc]
  rw [schemeTestComparison_affine_refine, hj, ← Category.assoc, hi, Category.assoc,
    ← Category.assoc ((pullback t).map (C.schemeTestComparison C' D i j w)),
    schemeTestComparison_affine_refine, Category.assoc]
  congr 1
  exact C.affineTestComparison_naturality C' (t ≫ i) (t ≫ j)
    (by simpa only [Category.assoc] using congrArg (t ≫ ·) w) D E f hf

end FLT.Mazur.SchemeAffineDescent.Chart
