/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertCommonAmbientEnvelope

/-!
# The common ambient source is an actual cartesian restriction

The envelope square is a scheme pullback, so it preserves scheme structure
and arbitrary test maps, not just points. Its open image is obtained by
restricting the original acyclic source envelope to one ambient Hilbert chart.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ) (V : Over (Spec (.of R)))
local notation "A" => allAffineAmbientCharts f

/-- Include the single ambient Hilbert product in the full parameter product. -/
def commonAmbientProductInclusion (U : (A).Index) :
    prod (commonAmbientHilbertTest f d U) V ⟶ prod (ampleHilbertTest f d) V :=
  prod.map (commonAmbientHilbertInclusion f d U) (𝟙 V)

instance (U : (A).Index) : IsOpenImmersion (commonAmbientProductInclusion f d V U).left :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_prod_fst_with_id (commonAmbientHilbertInclusion f d U) V).map
      (Over.forget _))
    (inferInstanceAs (IsOpenImmersion (commonAmbientHilbertInclusion f d U).left))

omit [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] in
/-- The product inclusion imposes only the ambient Hilbert coordinate condition. -/
theorem commonAmbientProductInclusion_range (U : (A).Index) :
    (commonAmbientProductInclusion f d V U).left.opensRange =
      (prod.fst : prod (ampleHilbertTest f d) V ⟶ ampleHilbertTest f d).left ⁻¹ᵁ
        ((A).hilbertChart d U).opensRange := by
  apply TopologicalSpace.Opens.ext
  simp only [Scheme.Hom.coe_preimage, Scheme.Hom.coe_opensRange]
  have h := Scheme.image_preimage_eq_of_isPullback
    ((IsPullback.of_prod_fst_with_id (commonAmbientHilbertInclusion f d U) V).map
      (Over.forget _)) Set.univ
  simp only [Set.preimage_univ, Set.image_univ, Over.forget_obj, Over.forget_map] at h
  convert h using 1 <;> rfl

/-- Pulling back the ambient product image recovers the actual original source support open. -/
theorem commonAmbientProductInclusion_preimage (U : (A).Index) :
    (variableFullHilbertEnvelope f d V).left ⁻¹ᵁ
        (commonAmbientProductInclusion f d V U).left.opensRange =
      (commonAmbientSourceInclusion f d V U).left.opensRange := by
  rw [commonAmbientProductInclusion_range, ← Scheme.Hom.comp_preimage,
    ← Over.comp_left, variableFullHilbertEnvelope_fst]
  change commonAmbientSourceOpen f d V U = (commonAmbientSourceOpen f d V U).ι.opensRange
  rw [Scheme.Opens.opensRange_ι]

/-- The source envelope square is cartesian as a square of actual schemes. -/
theorem commonAmbientSourceEnvelope_isPullback (U : (A).Index) :
    IsPullback (commonAmbientSourceEnvelope f d V U).left
      (commonAmbientSourceInclusion f d V U).left
      (commonAmbientProductInclusion f d V U).left
      (variableFullHilbertEnvelope f d V).left :=
  IsOpenImmersion.isPullback _ _ _ _
    (congrArg Over.Hom.left (commonAmbientSourceEnvelope_fac f d V U)).symm
    (commonAmbientProductInclusion_preimage f d V U)

/-- The source envelope has exactly the full source's image inside the common ambient product. -/
theorem commonAmbientSourceEnvelope_range (U : (A).Index) :
    (commonAmbientSourceEnvelope f d V U).left.opensRange =
      (commonAmbientProductInclusion f d V U).left ⁻¹ᵁ
        (variableFullHilbertEnvelope f d V).left.opensRange := by
  apply TopologicalSpace.Opens.ext
  simp only [Scheme.Hom.coe_preimage, Scheme.Hom.coe_opensRange]
  have h := Scheme.image_preimage_eq_of_isPullback
    (commonAmbientSourceEnvelope_isPullback f d V U).flip Set.univ
  simpa only [Set.preimage_univ, Set.image_univ] using h

end FLT.Mazur.HilbertChart
