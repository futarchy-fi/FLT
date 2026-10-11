/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothHilbertRelationOperations
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# The original Picard sheaf as the quotient of its actual smooth relation

The source map is an effective epimorphism of fppf sheaves and its represented
kernel pair has the original sheaf as coequalizer. This does not assert that
the coequalizer is represented by a scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel FCurve SchemePicard OrderedCurvePower
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)

/-- The unchanged original fppf sheaf with its group structure forgotten. -/
def smoothHilbertTargetSheaf : Sheaf (Scheme.fppfTopology.over (Spec (.of R))) (Type 1) :=
  (sheafCompose (Scheme.fppfTopology.over (Spec (.of R)))
    (forget CommGrpCat.{1})).obj (relativeFppfSheaf f)

/-- The original source map considered as a morphism of fppf sheaves. -/
def smoothHilbertSourceSheafMap :
    (Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.obj (smoothHilbertSource f) ⟶
      smoothHilbertTargetSheaf f :=
  ⟨smoothHilbertSourceMap f hB⟩

/-- The sheaf presentation retains the proved local surjectivity. -/
instance smoothHilbertSourceSheafMap_isLocallySurjective :
    Sheaf.IsLocallySurjective (smoothHilbertSourceSheafMap f hB) :=
  smoothHilbertSourceMap_isLocallySurjective f hB

/-- The source map is an effective epimorphism in the original fppf sheaf category. -/
instance smoothHilbertSourceSheafMap_effectiveEpi :
    EffectiveEpi (smoothHilbertSourceSheafMap f hB) := by
  rw [← isRegularEpi_iff_effectiveEpi]
  exact IsRegularEpiCategory.regularEpiOfEpi _

/-- The actual relation also gives the kernel pair in original fppf sheaves. -/
theorem smoothHilbertRelation_sheaf_isPullback :
    IsPullback
      ((Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map
        (smoothHilbertRelationFst f hB))
      ((Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map
        (smoothHilbertRelationSnd f hB))
      (smoothHilbertSourceSheafMap f hB) (smoothHilbertSourceSheafMap f hB) := by
  apply IsPullback.of_map_of_faithful (sheafToPresheaf _ (Type 1))
  exact smoothHilbertRelation_isPullback f hB

/-- The canonical cofork from the actual relation to the original Picard sheaf. -/
def smoothHilbertSheafCofork :
    Cofork
      ((Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map
        (smoothHilbertRelationFst f hB))
      ((Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map
        (smoothHilbertRelationSnd f hB)) :=
  Cofork.ofπ (smoothHilbertSourceSheafMap f hB)
    (smoothHilbertRelation_sheaf_isPullback f hB).w

/-- The original Picard sheaf is the coequalizer of the actual smooth equivalence relation. -/
def smoothHilbertSheafCoforkIsColimit : IsColimit (smoothHilbertSheafCofork f hB) :=
  isColimitCoforkOfEffectiveEpi (smoothHilbertSourceSheafMap f hB) _
    (smoothHilbertRelation_sheaf_isPullback f hB).isLimit

end FLT.Mazur.HilbertChart
