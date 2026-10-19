/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SmoothCurveValuationStalk
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Dominant maps from integral schemes to smooth integral field curves are flat

Dominance injects actual sections, hence actual stalks. The target stalks
are valuation domains, so torsion freeness implies flatness there.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) [QuasiCompact f] [IsDominant f]

/-- Dominance between integral schemes injects each actual stalk map. -/
theorem dominantIntegral_stalkMap_injective (x : X) : Function.Injective (f.stalkMap x) := by
  let _ := IsSchemeTheoreticallyDominant.of_isDominant f
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show f x ∈ (Set.univ : Set Y) from trivial) isOpen_univ
  apply hU.stalkMap_injective f x hx
  intro g hg
  rw [Scheme.Hom.germ_stalkMap_apply] at hg
  have hzero : f.app U g = 0 :=
    (germ_injective_of_isIntegral X x hx) (hg.trans (map_zero _).symm)
  have hgzero : g = 0 := (f.app_injective U) (hzero.trans (map_zero _).symm)
  rw [hgzero, map_zero]

/-- The actual dominant map to a smooth integral curve is flat. -/
theorem dominantIntegral_smoothCurve_flat {K : Type u} [Field K]
    (s : Y ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 s] : Flat f := by
  apply Flat.of_stalkMap
  intro x
  let _ := smoothCurve_stalk_valuationRing s (f x)
  let _ := (f.stalkMap x).hom.toAlgebra
  let _ : Module.IsTorsionFree (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro a b hab
    change f.stalkMap x a * b = 0 at hab
    rcases mul_eq_zero.mp hab with ha | hb
    · exact Or.inl ((dominantIntegral_stalkMap_injective f x)
        (ha.trans (map_zero _).symm))
    · exact Or.inr hb
  change Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

end FLT.Mazur.FCurve
