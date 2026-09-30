/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveProductChartOverlaps
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# The Segre morphism of projective spaces

The affine Segre maps glue on the standard cover of the actual fiber product.
Their common coefficient map makes the resulting morphism a map over the base.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type (max u v)) [CommRing R] (ι κ : Type v)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The affine Segre maps agree on the actual intersections of product charts. -/
lemma segreChartToProjective_compatible (p q : ι × κ) :
    pullback.fst (productChartMap R ι κ p.1 p.2) (productChartMap R ι κ q.1 q.2) ≫
        segreChartToProjective R ι κ p.1 p.2 =
      pullback.snd (productChartMap R ι κ p.1 p.2) (productChartMap R ι κ q.1 q.2) ≫
        segreChartToProjective R ι κ q.1 q.2 := by
  apply (cancel_epi (productOverlapIso R ι κ p.1 q.1 p.2 q.2).hom).mp
  simpa only [productOverlapIso_hom_fst_assoc, productOverlapIso_hom_snd_assoc] using
    segreChartToProjective_overlap R ι κ p.1 q.1 p.2 q.2

/-- The Segre morphism between the existing projective-space schemes. -/
def segreMorphism : productSpace R ι κ ⟶ space R (ι × κ) :=
  (productChartCover R ι κ).glueMorphisms
    (fun p ↦ segreChartToProjective R ι κ p.1 p.2)
    (segreChartToProjective_compatible R ι κ)

/-- On each product chart the glued morphism is the affine Segre map. -/
@[reassoc (attr := simp)]
lemma productChartMap_segreMorphism (i : ι) (j : κ) :
    productChartMap R ι κ i j ≫ segreMorphism R ι κ =
      segreChartToProjective R ι κ i j :=
  (productChartCover R ι κ).ι_glueMorphisms _ _ (i, j)

/-- The local formula in terms of the actual chart-ring homomorphism. -/
lemma productChartMap_segreMorphism_eq (i : ι) (j : κ) :
    productChartMap R ι κ i j ≫ segreMorphism R ι κ =
      Spec.map (CommRingCat.ofHom (segreChartMap R ι κ i j).toRingHom) ≫
        chartMap R (ι × κ) (i, j) := by
  rw [productChartMap_segreMorphism]
  rfl

/-- The affine Segre maps preserve coefficients. -/
@[reassoc]
lemma segreChartToProjective_baseProjection (i : ι) (j : κ) :
    segreChartToProjective R ι κ i j ≫ baseProjection R (ι × κ) =
      Spec.map (CommRingCat.ofHom (algebraMap R (segreSourceRing R ι κ i j))) := by
  change (Spec.map (CommRingCat.ofHom (segreChartMap R ι κ i j).toRingHom) ≫
    chartMap R (ι × κ) (i, j)) ≫ _ = _
  rw [Category.assoc, chartMap_baseProjection, specAlgHom_base]

set_option maxHeartbeats 800000 in
-- Chartwise equality unfolds the tensor cover in independent coefficient and index universes.
/-- The global Segre morphism is a morphism over the coefficient spectrum. -/
@[reassoc]
lemma segreMorphism_baseProjection :
    segreMorphism R ι κ ≫ baseProjection R (ι × κ) =
      pullback.fst (baseProjection R ι) (baseProjection R κ) ≫ baseProjection R ι := by
  apply (productChartCover R ι κ).hom_ext _ _
  intro p
  change productChartMap R ι κ p.1 p.2 ≫ _ = productChartMap R ι κ p.1 p.2 ≫ _
  rw [productChartMap_segreMorphism_assoc, segreChartToProjective_baseProjection,
    productChartMap_fst_assoc, chartMap_baseProjection]
  exact (specAlgHom_base R
    (Algebra.TensorProduct.includeLeft : chartRing R ι p.1 →ₐ[R]
      segreSourceRing R ι κ p.1 p.2)).symm

end FLT.Mazur.ProjectiveSpace
