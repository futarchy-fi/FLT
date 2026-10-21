/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarImageQuotient
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Geometry inherited by the exact scalar image

The full image projection is surjective precisely when the original affine
source has closed image. Integral scalar morphisms satisfy this automatically.
Etaleness and finiteness descend through the fixed closed image inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarImageQuotient
set_option backward.isDefEq.respectTransparency false
variable {S : Type} [CommRing S] {X : Scheme.{0}} (b : X ⟶ Spec (.of S))

/-- Surjectivity of the full image projection identifies the original image exactly. -/
theorem range_eq_inclusion_of_surjective [Surjective (projection b)] :
    Set.range b = Set.range (inclusion b) := by
  conv_lhs => rw [← projection_inclusion b]
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (projection b).surjective, Set.image_univ]

/-- Closedness of the original affine source image supplies every full-image point. -/
theorem projection_surjective_of_isClosed_range [IsAffine X]
    (h : IsClosed (Set.range b)) : Surjective (projection b) := by
  constructor
  intro y
  have hy : inclusion b y ∈ Set.range b := by
    rw [← h.closure_eq, ← inclusion_range b]
    exact ⟨y, rfl⟩
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, (inclusion b).isClosedEmbedding.injective ?_⟩
  change (projection b ≫ inclusion b) x = inclusion b y
  rwa [projection_inclusion]

/-- For the affine full source, closed original image is the exact surjectivity condition. -/
theorem projection_surjective_iff [IsAffine X] :
    Surjective (projection b) ↔ IsClosed (Set.range b) := by
  constructor
  · intro h
    let _ := h
    rw [range_eq_inclusion_of_surjective b]
    exact (inclusion b).isClosedEmbedding.isClosed_range
  · exact projection_surjective_of_isClosed_range b

/-- Etaleness survives factoring through the exact, possibly nonreduced image. -/
theorem projection_etale [Etale b] : Etale (projection b) := by
  have : Etale (projection b ≫ inclusion b) := by rwa [projection_inclusion]
  exact Etale.of_comp _ (inclusion b)

/-- Integral original scalar geometry gives integral full-image geometry. -/
theorem projection_integral [IsIntegralHom b] : IsIntegralHom (projection b) := by
  have : IsIntegralHom (projection b ≫ inclusion b) := by rwa [projection_inclusion]
  exact IsIntegralHom.of_comp _ (inclusion b)

/-- Finite original scalar geometry gives a finite full-image projection. -/
theorem projection_finite [IsFinite b] : IsFinite (projection b) := by
  have : IsFinite (projection b ≫ inclusion b) := by rwa [projection_inclusion]
  exact IsFinite.of_comp _ (inclusion b)

/-- Integrality covers every point of the exact image, without radicalizing its equations. -/
theorem projection_surjective_of_integral [IsIntegralHom b] : Surjective (projection b) := by
  let _ : IsAffine X := isAffine_of_isAffineHom b
  exact projection_surjective_of_isClosed_range b b.isClosedMap.isClosed_range

end FLT.Mazur.SchemeScalarImageQuotient
