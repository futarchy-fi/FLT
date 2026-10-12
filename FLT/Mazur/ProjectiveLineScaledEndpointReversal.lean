/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineEndpointReversal
public import FLT.Mazur.ProjectiveLineScaledReciprocalGluing
public import FLT.Mazur.ProjectiveLineValuationExtension
public import FLT.Mazur.ProjectiveLineOpenChartExclusion

/-!
# Full projective reversal with the original Laurent scale

The projective map extends T ↦ c/T, and hence exchanges the two endpoints.
The dense torus detects equality of maps over a separated target.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K : Type u) [Field K]

/-- Reciprocal projective coordinates retain their specified nonzero scale. -/
def scaledEndpointReversal (c : Kˣ) : scheme K ⟶ scheme K :=
  endpointReversal K ≫ scaling K c

/-- The whole Laurent torus carries exactly the scaled reciprocal. -/
@[reassoc] theorem torus_scaledEndpointReversal (c : Kˣ) :
    overlapLeft K ≫ left K ≫ scaledEndpointReversal K c =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.reciprocal c).toRingHom) ≫
        overlapLeft K ≫ left K := by
  rw [scaledReciprocal_overlap_assoc, ← left_scaling,
    scaledEndpointReversal, left_endpointReversal_assoc,
    ← Category.assoc, endpointReversal_overlap, Category.assoc]

/-- The complete reciprocal map fixes the coefficient projection. -/
@[reassoc] theorem scaledEndpointReversal_toBase (c : Kˣ) :
    scaledEndpointReversal K c ≫ toBase K = toBase K := by
  rw [scaledEndpointReversal, Category.assoc, scaling_toBase, endpointReversal_toBase]

/-- The original zero endpoint goes to infinity. -/
@[reassoc] theorem zero_scaledEndpointReversal (c : Kˣ) :
    zero K ≫ scaledEndpointReversal K c = infinity K := by
  rw [scaledEndpointReversal, zero_endpointReversal_assoc, infinity_scaling]

/-- The original infinity endpoint goes to zero. -/
@[reassoc] theorem infinity_scaledEndpointReversal (c : Kˣ) :
    infinity K ≫ scaledEndpointReversal K c = zero K := by
  rw [scaledEndpointReversal, infinity_endpointReversal_assoc, zero_scaling]

/-- Agreement on the full Laurent torus extends over both projective endpoints. -/
theorem torus_hom_ext {X B : Scheme.{u}} (b : X ⟶ B) [IsSeparated b]
    {f g : scheme K ⟶ X} (hb : f ≫ b = g ≫ b)
    (h : overlapLeft K ≫ left K ≫ f = overlapLeft K ≫ left K ≫ g) : f = g := by
  let _ : IsDominant (overlapLeft K ≫ left K) := ⟨openChart_denseRange K _⟩
  exact ext_of_isDominant_of_isSeparated b hb (overlapLeft K ≫ left K)
    (by simpa only [Category.assoc] using h)

end FLT.Mazur.ProjectiveLine
