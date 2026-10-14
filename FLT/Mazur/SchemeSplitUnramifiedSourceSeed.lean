/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeSplitEtaleSourceSeed
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-!
# Split seeds without flatness of the coefficient morphism

The graph of an etale source neighborhood is open in the complete coefficient
pullback when the coefficient morphism is formally unramified of finite type.
Its new coefficient map is the identity. No flatness of the old coefficients,
monicity of the old seed, or reduction of any scheme is required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeSplitEtaleSourceSeed
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {A T Z : Scheme.{u}} (w : A ⟶ T) (a : Z ⟶ A)
  [FormallyUnramified w] [LocallyOfFiniteType w] [Etale a]

/-- An unramified old coefficient map suffices for an actual open graph seed. -/
theorem seed_isOpenImmersion_of_unramified : IsOpenImmersion (seed w a) := by
  let _ : Etale (seed w a ≫ toSource w a) := by rw [seed_toSource]; infer_instance
  let _ : FormallyUnramified (a ≫ w) :=
    MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  let _ : FormallyUnramified (toSource w a) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  let _ : LocallyOfFiniteType (toSource w a) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst w (a ≫ w)))
  let _ := Etale.of_comp (seed w a) (toSource w a)
  exact IsOpenImmersion.of_flat_of_mono _

/-- The split seed is etale over the complete changed source without old flatness. -/
theorem seed_etale_of_unramified : Etale (seed w a) := by
  let _ := seed_isOpenImmersion_of_unramified w a
  infer_instance

omit [Etale a] in
/-- Choosing the original source itself constructs a seed through every original point. -/
theorem diagonal_seed_geometry :
    IsOpenImmersion (seed w (𝟙 A)) ∧
      seed w (𝟙 A) ≫ projection w (𝟙 A) = 𝟙 A ∧
      ∀ x : A, toSource w (𝟙 A) (seed w (𝟙 A) x) = x := by
  refine ⟨seed_isOpenImmersion_of_unramified w (𝟙 A), seed_projection w (𝟙 A), ?_⟩
  intro x
  exact seed_point w (𝟙 A) x

end FLT.Mazur.SchemeSplitEtaleSourceSeed
