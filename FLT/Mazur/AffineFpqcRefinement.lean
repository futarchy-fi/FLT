/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Cover.Sigma
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Affine refinement of a faithfully flat quasi-compact morphism

Over an affine target, a finite affine refinement of an fpqc morphism has
an affine disjoint union. Its structural map is faithfully flat. The actual
factorization through the original cover is retained for pullback arguments.
No openness or finite-presentation hypothesis on the original cover is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {T S : Scheme.{u}} [IsAffine S]

/-- An fpqc morphism over an affine base admits an affine faithfully flat refinement. -/
theorem exists_affine_fpqc_refinement (g : T ⟶ S)
    [Flat g] [Surjective g] [QuasiCompact g] :
    ∃ (Z : Scheme.{u}) (_ : IsAffine Z) (k : Z ⟶ T),
      Flat (k ≫ g) ∧ Surjective (k ≫ g) := by
  let C := g.cover (P := @Flat) inferInstance
  obtain ⟨D, a, hfin, _⟩ := QuasiCompactCover.exists_hom C
  let : Finite D.cover.I₀ := hfin
  have (i : D.cover.I₀) : IsAffine (D.cover.X i) := inferInstanceAs (IsAffine (Spec _))
  let k : (∐ D.cover.X) ⟶ T := Sigma.desc (fun i ↦ a.h₀ i)
  have hk : k ≫ g = Sigma.desc D.cover.f := by
    apply Sigma.hom_ext
    intro i
    simpa only [k, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc] using
      (show a.h₀ i ≫ g = D.cover.f i from a.w₀ i)
  refine ⟨∐ D.cover.X, inferInstance, k, ?_, ?_⟩
  · rw [hk]
    exact D.cover.sigma.map_prop default
  · rw [hk]
    infer_instance

end FLT.Mazur.FCurve
