/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicParameterSource
public import Mathlib.CategoryTheory.Sites.RegularEpi

/-!
# The actual disjoint source presents the unmarked fppf sheaf

The fixed-chart parameter presheaf sheafifies to the sheaf represented by
the actual disjoint source scheme. Transporting the full quotient map gives
an effective epimorphism from this represented source. Its values retain
the original parameters even on disconnected tests.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Sheafification extends the actual parameter-to-source comparison. -/
def parameterSourceSheafLift :
    (presheafToSheaf Scheme.fppfTopology (Type 1)).obj (normalizedParameterPresheaf n) ⟶
      Scheme.fppfTopology.uliftYoneda.{1}.obj (normalizedDisjointSource n) :=
  ⟨sheafifyLift Scheme.fppfTopology (parameterToDisjointSource n)
    (Scheme.fppfTopology.uliftYoneda.obj (normalizedDisjointSource n)).property⟩

/-- The lifted comparison retains every actual original parameter. -/
theorem parameterSourceSheafLift_unit :
    toSheafify Scheme.fppfTopology (normalizedParameterPresheaf n) ≫
      (parameterSourceSheafLift n).hom = parameterToDisjointSource n :=
  toSheafify_sheafifyLift _ _ _

/-- The actual scheme coproduct represents the sheafification of fixed-chart parameters. -/
instance parameterSourceSheafLift_isIso : IsIso (parameterSourceSheafLift n) := by
  have hi : Presheaf.IsLocallyInjective Scheme.fppfTopology
      (toSheafify Scheme.fppfTopology (normalizedParameterPresheaf n) ≫
        (parameterSourceSheafLift n).hom) := by
    rw [parameterSourceSheafLift_unit]
    infer_instance
  have hs : Presheaf.IsLocallySurjective Scheme.fppfTopology
      (toSheafify Scheme.fppfTopology (normalizedParameterPresheaf n) ≫
        (parameterSourceSheafLift n).hom) := by
    rw [parameterSourceSheafLift_unit]
    infer_instance
  apply (Sheaf.isLocallyBijective_iff_isIso (parameterSourceSheafLift n)).mp
  exact ⟨(Presheaf.comp_isLocallyInjective_iff _ _ _).mp hi,
    (Presheaf.comp_isLocallySurjective_iff _ _ _).mp hs⟩

/-- The actual disjoint source maps to the constructed full unmarked sheaf quotient. -/
def unmarkedDisjointSourceMap :
    Scheme.fppfTopology.uliftYoneda.{1}.obj (normalizedDisjointSource n) ⟶
      unmarkedParameterSheaf n :=
  inv (parameterSourceSheafLift n) ≫
    (presheafToSheaf Scheme.fppfTopology (Type 1)).map (unmarkedParameterProjection n)

/-- The map from the represented source has exactly the original parameter values. -/
theorem parameterToDisjointSource_unmarked :
    parameterToDisjointSource n ≫ (unmarkedDisjointSourceMap n).hom =
      unmarkedParameterSheafMap n := by
  have hinv : (parameterSourceSheafLift n).hom ≫ (inv (parameterSourceSheafLift n)).hom =
      𝟙 _ := congrArg (fun a ↦ a.hom) (IsIso.hom_inv_id (parameterSourceSheafLift n))
  change parameterToDisjointSource n ≫ ((inv (parameterSourceSheafLift n)).hom ≫
    sheafifyMap _ (unmarkedParameterProjection n)) =
      unmarkedParameterProjection n ≫ toSheafify _ _
  rw [← parameterSourceSheafLift_unit, Category.assoc, ← Category.assoc
    (parameterSourceSheafLift n).hom, hinv, Category.id_comp, ← toSheafify_naturality]

/-- The represented source covers every section of the full unmarked quotient fppf locally. -/
instance unmarkedDisjointSourceMap_isLocallySurjective :
    Sheaf.IsLocallySurjective (unmarkedDisjointSourceMap n) := by
  have : Sheaf.IsLocallySurjective
      ((presheafToSheaf Scheme.fppfTopology (Type 1)).map (unmarkedParameterProjection n)) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff _ _).mpr inferInstance
  unfold unmarkedDisjointSourceMap
  infer_instance

/-- The original single scheme source is an effective epimorphism in fppf sheaves. -/
instance unmarkedDisjointSourceMap_effectiveEpi : EffectiveEpi (unmarkedDisjointSourceMap n) := by
  rw [← isRegularEpi_iff_effectiveEpi]
  exact IsRegularEpiCategory.regularEpiOfEpi _

end FLT.Mazur.CyclicCharacteristicAtlas
