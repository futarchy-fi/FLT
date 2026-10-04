/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalAffineRefinement

/-!
# Retaining evaluated points under principal refinement

An element with unit value at a specified field-valued point can be inverted
without losing that point. Compatible evaluations identify the retained point
with the original point before any refinement.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.EvaluatedPrincipalRefinement
open PrincipalAffineRefinement
variable {R K : Type u} [CommRing R] [Field K] {X : Scheme.{u}}

/-- A unit evaluation puts every point over that evaluation in the basic open. -/
lemma mem_basicOpen (e : R →+* K) (t : R) (ht : IsUnit (e t)) (x : Spec (.of K)) :
    Spec.map (CommRingCat.ofHom e) x ∈ PrimeSpectrum.basicOpen t := by
  have : x.asIdeal.IsPrime := x.isPrime
  exact x.asIdeal.notMem_of_isUnit ht

/-- The chosen field-valued point survives the actual localization chart. -/
lemma mem_range (j : Spec (.of R) ⟶ X) (e : R →+* K)
    (t : R) (ht : IsUnit (e t)) (x : Spec (.of K)) :
    (Spec.map (CommRingCat.ofHom e) ≫ j) x ∈ Set.range (chart j t) :=
  mem_range_chart j t _ (mem_basicOpen e t ht x)

/-- Compatibility on numerators identifies the localized point geometrically. -/
@[reassoc]
lemma evaluation_chart (j : Spec (.of R) ⟶ X) (e : R →+* K) (s : R)
    (E : Localization.Away s →+* K)
    (hE : E.comp (algebraMap R (Localization.Away s)) = e) :
    Spec.map (CommRingCat.ofHom E) ≫ chart j s = Spec.map (CommRingCat.ofHom e) ≫ j := by
  unfold chart inclusion
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hE]

end FLT.Mazur.EvaluatedPrincipalRefinement
