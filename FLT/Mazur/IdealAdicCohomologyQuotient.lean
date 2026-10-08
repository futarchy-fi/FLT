/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicCohomologyImage
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Cohomology modulo the actual image filtration

Quotient cohomology embeds in the cohomology of the coefficient quotient.
Its image consists exactly of classes lifted from the original coefficient.
The embeddings commute with all reductions of the ideal-adic tower.
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

/-- The quotient of original cohomology by the actual image of ideal-power cohomology. -/
abbrev imageQuotient (q n : ℕ) := ModuleRingH ρ M q ⧸ cohomologyImage ρ I M q n

/-- Restriction to the coefficient quotient descends through the actual image filtration. -/
def imageQuotientComparison (q n : ℕ) :
    imageQuotient ρ I M q n →ₗ[R] ModuleRingH ρ (quotient I M n) q :=
  (cohomologyImage ρ I M q n).liftQ
    ((moduleRingHFunctor ρ q).map (projection I M n)).hom
    (cohomologyImage_eq_ker ρ I M q n).le

/-- The comparison retains the original restriction on cohomology classes. -/
lemma imageQuotientComparison_mk (q n : ℕ) (x : ModuleRingH ρ M q) :
    imageQuotientComparison ρ I M q n (Submodule.Quotient.mk x) =
      moduleHMap (projection I M n) q x := rfl

/-- Exactness makes the descended comparison injective. -/
theorem imageQuotientComparison_injective (q n : ℕ) :
    Function.Injective (imageQuotientComparison ρ I M q n) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot' _ _ (cohomologyImage_eq_ker ρ I M q n)

/-- The image quotient identifies with the actual range of cohomological restriction. -/
def imageQuotientRangeEquiv (q n : ℕ) :
    imageQuotient ρ I M q n ≃ₗ[R]
      LinearMap.range ((moduleRingHFunctor ρ q).map (projection I M n)).hom :=
  (Submodule.quotEquivOfEq _ _ (cohomologyImage_eq_ker ρ I M q n)).trans
    ((moduleRingHFunctor ρ q).map (projection I M n)).hom.quotKerEquivRange

/-- Reduction between quotients of the original cohomology. -/
def imageQuotientReduction (q : ℕ) {a b : ℕ} (h : a ≤ b) :
    imageQuotient ρ I M q b →ₗ[R] imageQuotient ρ I M q a :=
  (cohomologyImage ρ I M q b).mapQ (cohomologyImage ρ I M q a) LinearMap.id
    (cohomologyImage_antitone ρ I M q h)

/-- Quotient reduction preserves representatives from the original cohomology. -/
lemma imageQuotientReduction_mk (q : ℕ) {a b : ℕ} (h : a ≤ b)
    (x : ModuleRingH ρ M q) :
    imageQuotientReduction ρ I M q h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := rfl

/-- The comparison commutes with every actual ideal-adic quotient reduction. -/
lemma imageQuotientComparison_reduction (q : ℕ) {a b : ℕ} (h : a ≤ b)
    (x : imageQuotient ρ I M q b) :
    moduleHMap (reduction I M h) q (imageQuotientComparison ρ I M q b x) =
      imageQuotientComparison ρ I M q a (imageQuotientReduction ρ I M q h x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change moduleHMap (reduction I M h) q (moduleHMap (projection I M b) q x) =
      moduleHMap (projection I M a) q x
    rw [← LinearMap.comp_apply, ← moduleHMap_comp, projection_reduction]

end FLT.Mazur.IdealAdicQuotient
