/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionProjectiveImmersion
public import Mathlib.RingTheory.FiniteType

/-!
# Finite algebra generators and projective chart surjectivity

Finite type supplies actual finite sets of chart functions. When they are
ratios of global sections, the projective chart ring map is surjective.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.FCurve

/-- A finite-type ring map has finitely many generators together with its scalar image. -/
theorem finiteType_ring_generators {R A : Type*} [CommRing R] [CommRing A]
    (r : R →+* A) (hr : r.FiniteType) :
    ∃ G : Finset A, Subring.closure (Set.range r ∪ (G : Set A)) = ⊤ := by
  let := r.toAlgebra
  let : Algebra.FiniteType R A := hr
  obtain ⟨G, hG⟩ := Algebra.FiniteType.out (R := R) (A := A)
  refine ⟨G, ?_⟩
  change Subring.closure (Set.range (algebraMap R A) ∪ (G : Set A)) = ⊤
  rw [← Algebra.adjoin_eq_ring_closure, hG]
  rfl

open ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme.{u}} (L : X.Modules) {R : Type u} [CommRing R] (n : ℕ)
    (t : Fin (n + 1) → Γ(L, ⊤))

/-- Algebra generators realized by section ratios make the actual chart map surjective. -/
theorem sectionProjectiveChartRingMap_surjective (i : Fin (n + 1)) (U : X.Opens)
    (hi : U ≤ sectionGeneratorOpen L (t i)) (r : R →+* Γ(X, U)) (G : Set Γ(X, U))
    (hG : Subring.closure (Set.range r ∪ G) = ⊤)
    (ht : ∀ a ∈ G, ∃ j, sectionRatioOn L (t i) U hi (t j) = a) :
    Function.Surjective (sectionProjectiveChartRingMap L n t i U hi r) := by
  let φ := sectionProjectiveChartRingMap L n t i U hi r
  have hle : Subring.closure (Set.range r ∪ G) ≤ φ.range := by
    apply Subring.closure_le.mpr
    rintro a (⟨b, rfl⟩ | ha)
    · exact ⟨chartScalars R (Fin (n + 1)) i b,
        sectionProjectiveChartRingMap_scalar L n t i U hi r b⟩
    · obtain ⟨j, hj⟩ := ht a ha
      exact ⟨coordinate R (Fin (n + 1)) i j,
        (sectionProjectiveChartRingMap_coordinate L n t i U hi r j).trans hj⟩
  rw [hG] at hle
  intro a
  exact hle (show a ∈ (⊤ : Subring Γ(X, U)) from trivial)

end FLT.Mazur.FCurve
