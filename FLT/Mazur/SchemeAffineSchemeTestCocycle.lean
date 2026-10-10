/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineSchemeTestComparison

/-!
# Global cocycle for comparisons on scheme tests

Equality is detected on an affine open cover of the test scheme. Each of the
three pulled-back maps normalizes to the effective affine-test comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y W : Scheme.{u}} {p : Y ⟶ X}
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
attribute [local irreducible] sheaf CrossRefinement.effectiveComparison
  baseOverlapComparison schemeTestComparison affineTestComparison

/-- The actual glued pair comparisons obey the cocycle on every test scheme. -/
theorem schemeTestComparison_cocycle (T : Fin 3 → Chart p)
    (a : W ⟶ X) (b : ∀ i, W ⟶ Spec (T i).baseRing)
    (h : ∀ i, b i ≫ (T i).base = a)
    [∀ i, ((pullback (T i).cover).obj M).IsQuasicoherent] :
    (T 0).schemeTestComparison (T 1) D (b 0) (b 1) ((h 0).trans (h 1).symm) ≫
      (T 1).schemeTestComparison (T 2) D (b 1) (b 2) ((h 1).trans (h 2).symm) =
      (T 0).schemeTestComparison (T 2) D (b 0) (b 2) ((h 0).trans (h 2).symm) := by
  apply ModuleSheafOpenImmersionGluing.hom_ext
    (fun i ↦ Spec (W.affineOpenCover.X i)) W.affineOpenCover.f
    (fun x ↦ ⟨W.affineOpenCover.idx x, W.affineOpenCover.covers x⟩)
  intro k
  apply (cancel_mono ((pullbackComp (W.affineOpenCover.f k) (b 2)).hom.app
    ((T 2).sheaf D))).mp
  rw [Functor.map_comp, Category.assoc, schemeTestComparison_affine_refine,
    ← Category.assoc, schemeTestComparison_affine_refine, Category.assoc,
    schemeTestComparison_affine_refine]
  congr 1
  exact affineTestComparison_cocycle D T (W.affineOpenCover.f k ≫ a)
    (fun i ↦ W.affineOpenCover.f k ≫ b i)
    (fun i ↦ by rw [Category.assoc, h i])

end FLT.Mazur.SchemeAffineDescent.Chart
