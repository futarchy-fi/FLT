/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveOverlapModuleLocalization

/-!
# Point membership in projective charts

A spectrum presentation tests membership in another standard chart by the
corresponding coordinate in the source prime ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {R S : Type u} [CommRing R] [CommRing S] {ι : Type u}

/-- Chart membership for a morphism presented by an actual chart ring map. -/
lemma spec_chartMap_mem_iff (i j : ι) (f : chartRing R ι i →+* S)
    (x : Spec (.of S)) :
    (Spec.map (CommRingCat.ofHom f) ≫ chartMap R ι i) x ∈ chart R ι j ↔
      f (coordinate R ι i j) ∉ x.asIdeal := by
  change x ∈ (Spec.map (CommRingCat.ofHom f) ≫ chartMap R ι i) ⁻¹ᵁ chart R ι j ↔ _
  rw [Scheme.Hom.comp_preimage, chartMap_preimage_chart, SpecMap_preimage_basicOpen]
  rfl

/-- At a field-valued point the chart condition is nonzero evaluation. -/
lemma field_chartMap_mem_iff {K : Type u} [Field K] (i j : ι)
    (f : chartRing R ι i →+* K) (x : Spec (.of K)) :
    (Spec.map (CommRingCat.ofHom f) ≫ chartMap R ι i) x ∈ chart R ι j ↔
      f (coordinate R ι i j) ≠ 0 := by
  rw [spec_chartMap_mem_iff]
  let := x.isPrime
  rw [show x.asIdeal = ⊥ from Ideal.eq_bot_of_prime x.asIdeal]
  rfl

end FLT.Mazur.ProjectiveSpace
