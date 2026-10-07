/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineDescentChart

/-!
# Identity and composition of geometric affine chart refinements

Refinements compose by composing their coordinate ring maps. Their equations
over the original base and cover follow from contravariance of spectrum.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart.Refinement
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {C C' C'' C''' : Chart p}

/-- The identity geometric refinement of an affine chart. -/
def identity (C : Chart p) : C.Refinement C where
  base := 𝟙 _
  cover := 𝟙 _
  square := by simp
  base_over := by simp
  cover_over := by simp

/-- Compose geometric refinements, retaining both factorizations over the scheme cover. -/
def comp (ρ : C.Refinement C') (σ : C'.Refinement C'') : C.Refinement C'' where
  base := ρ.base ≫ σ.base
  cover := ρ.cover ≫ σ.cover
  square := by rw [← Category.assoc, ρ.square, Category.assoc, σ.square, Category.assoc]
  base_over := by rw [Spec.map_comp, Category.assoc, ρ.base_over, σ.base_over]
  cover_over := by rw [Spec.map_comp, Category.assoc, ρ.cover_over, σ.cover_over]

/-- The two coordinate maps determine a refinement. -/
@[ext]
theorem ext {ρ σ : C.Refinement C'} (ha : ρ.base = σ.base) (hb : ρ.cover = σ.cover) :
    ρ = σ := by
  cases ρ
  cases σ
  cases ha
  cases hb
  rfl

/-- Identity on the source preserves refinements. -/
@[simp]
theorem identity_comp (ρ : C.Refinement C') : (identity C).comp ρ = ρ := by
  ext <;> simp [identity, comp]

/-- Identity on the target preserves refinements. -/
@[simp]
theorem comp_identity (ρ : C.Refinement C') : ρ.comp (identity C') = ρ := by
  ext <;> simp [identity, comp]

/-- Composition of refinements is associative. -/
theorem comp_assoc (ρ : C.Refinement C') (σ : C'.Refinement C'')
    (τ : C''.Refinement C''') : (ρ.comp σ).comp τ = ρ.comp (σ.comp τ) := by
  ext <;> simp [comp, Category.assoc]

end FLT.Mazur.SchemeAffineDescent.Chart.Refinement
