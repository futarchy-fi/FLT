/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineStructuralStandardSmoothChart
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Étale coordinates over the unchanged affine base

A smooth scheme has affine open charts mapping étale to finite affine spaces
of possibly varying dimensions. The factorization keeps the original base map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineSmoothEtaleCoordinates

/-- Every smooth point has polynomial étale coordinates over its original affine base. -/
theorem exists_chart {R : Type} [CommRing R] {X : Scheme}
    (f : X ⟶ Spec (.of R)) [Smooth f] (x : X) :
    ∃ (A : CommRingCat) (n : ℕ) (g : MvPolynomial (Fin n) R →+* A)
      (j : Spec A ⟶ X),
      g.Etale ∧ IsOpenImmersion j ∧ x ∈ Set.range j ∧
        j ≫ f = Spec.map (CommRingCat.ofHom g) ≫
          Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin n) R)) := by
  obtain ⟨A, a, j, ha, hj, hx, hf⟩ :=
    AffineStructuralStandardSmoothChart.exists_chart f x
  obtain ⟨n, g, hg, he⟩ := ha.exists_etale_mvPolynomial
  refine ⟨A, n, g, j, he, hj, hx, ?_⟩
  rw [hf, ← Spec.map_comp]
  exact congrArg (fun k ↦ Spec.map (CommRingCat.ofHom k)) hg.symm

end FLT.Mazur.AffineSmoothEtaleCoordinates
