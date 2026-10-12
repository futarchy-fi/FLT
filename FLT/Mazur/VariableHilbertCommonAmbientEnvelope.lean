/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertCommonAmbientSource

/-!
# An actual product envelope for the common ambient source neighborhood

The original source open embeds into the product of its single ambient
Hilbert chart and the original translation scheme. Both coordinates and
the original coefficient map are retained. The product is not asserted affine.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ) (V : Over (Spec (.of R)))
local notation "A" => allAffineAmbientCharts f

/-- The original full source embeds into full Hilbert parameters times the translation base. -/
def variableFullHilbertEnvelope :
    variableHilbertTest f d V ⟶ prod (ampleHilbertTest f d) V :=
  (prod.braiding V (acyclicHilbertTest f d)).hom ≫ prod.map (acyclicHilbertArrow f d) (𝟙 V)

instance : IsOpenImmersion (variableFullHilbertEnvelope f d V).left := by
  let _ : IsOpenImmersion (prod.map (acyclicHilbertArrow f d) (𝟙 V)).left :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_prod_fst_with_id (acyclicHilbertArrow f d) V).map (Over.forget _))
      (inferInstanceAs (IsOpenImmersion (acyclicHilbertArrow f d).left))
  let _ : IsIso (prod.braiding V (acyclicHilbertTest f d)).hom.left :=
    ((Over.forget _).mapIso (prod.braiding V (acyclicHilbertTest f d))).isIso_hom
  change IsOpenImmersion ((prod.braiding V (acyclicHilbertTest f d)).hom.left ≫ _)
  infer_instance

/-- The envelope's first coordinate is the full original Hilbert parameter. -/
@[reassoc]
theorem variableFullHilbertEnvelope_fst :
    variableFullHilbertEnvelope f d V ≫ prod.fst = variableFullHilbertParameter f d V := by
  simp only [variableFullHilbertEnvelope, Category.assoc, prod.map_fst,
    prod.braiding, prod.lift_fst_assoc, variableFullHilbertParameter, variableHilbertParameter]

/-- The envelope's second coordinate is the independent original translation point. -/
@[reassoc]
theorem variableFullHilbertEnvelope_snd :
    variableFullHilbertEnvelope f d V ≫ prod.snd = variableHilbertBase f d V := by
  simp only [variableFullHilbertEnvelope, Category.assoc, prod.map_snd, Category.comp_id,
    prod.braiding, prod.lift_snd, variableHilbertBase]

/-- One original ambient Hilbert chart as an object over the original coefficient base. -/
def commonAmbientHilbertTest (U : (A).Index) : Over (Spec (.of R)) :=
  Over.mk ((A).chartBase d U)

/-- The actual inclusion of this ambient chart in the full Hilbert parameter scheme. -/
def commonAmbientHilbertInclusion (U : (A).Index) :
    commonAmbientHilbertTest f d U ⟶ ampleHilbertTest f d :=
  Over.homMk ((A).hilbertChart d U) ((A).hilbertChart_over d U)

instance (U : (A).Index) : IsOpenImmersion (commonAmbientHilbertInclusion f d U).left :=
  inferInstanceAs (IsOpenImmersion ((A).hilbertChart d U))

/-- The common source neighborhood maps into its single ambient chart times the full base. -/
def commonAmbientSourceEnvelope (U : (A).Index) :
    commonAmbientSourceTest f d V U ⟶ prod (commonAmbientHilbertTest f d U) V :=
  prod.lift (Over.homMk (commonAmbientSourceParameter f d V U)
    (commonAmbientSourceParameter_over f d V U))
    (commonAmbientSourceInclusion f d V U ≫ variableHilbertBase f d V)

/-- The source product envelope retains the original map into the full Hilbert product. -/
@[reassoc]
theorem commonAmbientSourceEnvelope_fac (U : (A).Index) :
    commonAmbientSourceEnvelope f d V U ≫ prod.map (commonAmbientHilbertInclusion f d U) (𝟙 V) =
      commonAmbientSourceInclusion f d V U ≫ variableFullHilbertEnvelope f d V := by
  apply prod.hom_ext
  · simp only [Category.assoc, prod.map_fst, variableFullHilbertEnvelope_fst,
      commonAmbientSourceEnvelope, prod.lift_fst_assoc]
    apply Over.OverMorphism.ext
    exact commonAmbientSourceParameter_fac f d V U
  · simp only [Category.assoc, prod.map_snd, Category.comp_id,
      variableFullHilbertEnvelope_snd, commonAmbientSourceEnvelope, prod.lift_snd]

instance (U : (A).Index) : IsOpenImmersion (commonAmbientSourceEnvelope f d V U).left := by
  let j := prod.map (commonAmbientHilbertInclusion f d U) (𝟙 V)
  let _ : IsOpenImmersion j.left := MorphismProperty.of_isPullback
    ((IsPullback.of_prod_fst_with_id (commonAmbientHilbertInclusion f d U) V).map
      (Over.forget _)) (inferInstanceAs
        (IsOpenImmersion (commonAmbientHilbertInclusion f d U).left))
  let _ : IsOpenImmersion ((commonAmbientSourceEnvelope f d V U).left ≫ j.left) := by
    rw [← Over.comp_left, commonAmbientSourceEnvelope_fac, Over.comp_left]
    infer_instance
  exact IsOpenImmersion.of_comp _ j.left

end FLT.Mazur.HilbertChart
