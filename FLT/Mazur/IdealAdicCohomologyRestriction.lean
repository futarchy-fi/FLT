/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicFormalComparison

/-!
# Restricting actual cohomology classes to the infinitesimal tower

The map uses the original quotient projections in every coordinate. It is
also the composite of the completion map and the formal comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.IdealAdicQuotient

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]

/-- Restrict an actual cohomology class along all the original quotient projections. -/
def cohomologyRestriction (q : ℕ) :
    ModuleRingH ρ M q →ₗ[R] compatibleCohomology ρ I M q where
  toFun x := ⟨fun n ↦ moduleHMap (projection I M n) q x, by
    intro a b hab
    change moduleHMap (reduction I M hab) q (moduleHMap (projection I M b) q x) = _
    rw [← LinearMap.comp_apply, ← moduleHMap_comp, projection_reduction]⟩
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact map_add (moduleHMap (projection I M n) q) x y
  map_smul' r x := by
    apply Subtype.ext
    funext n
    exact map_smul ((moduleRingHFunctor ρ q).map (projection I M n)).hom r x

/-- Evaluation is the original map on cohomology. -/
lemma cohomologyRestriction_eval (q n : ℕ) (x : ModuleRingH ρ M q) :
    (cohomologyRestriction ρ I M q x).val n = moduleHMap (projection I M n) q x := rfl

/-- Completion does not change the restriction map or any of its coordinates. -/
lemma formalComparison_comp_of (J : Ideal R)
    (hJ : ∀ (r : R), r ∈ J → ∀ U : X.affineOpens,
      X.presheaf.map U.1.leTop.op (ρ r) ∈ I.ideal U) (q : ℕ) :
    (formalComparison ρ I M J hJ q).comp (AdicCompletion.of J (ModuleRingH ρ M q)) =
      cohomologyRestriction ρ I M q := by
  ext x n
  rfl

/-- Bijectivity of the genuine restriction gives one unique algebraic class for a family. -/
theorem existsUnique_class_of_bijective (q : ℕ)
    (h : Function.Bijective (cohomologyRestriction ρ I M q))
    (x : compatibleCohomology ρ I M q) :
    ∃! y : ModuleRingH ρ M q, ∀ n, moduleHMap (projection I M n) q y = x.val n := by
  obtain ⟨y, hy⟩ := h.2 x
  refine ⟨y, fun n ↦ congrArg (fun z ↦ z.val n) hy, ?_⟩
  intro z hz
  apply h.1
  apply Subtype.ext
  funext n
  exact (hz n).trans (congrArg (fun z ↦ z.val n) hy).symm

end FLT.Mazur.IdealAdicQuotient
