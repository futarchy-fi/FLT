/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertQuotientFullRelation
public import FLT.Mazur.SmoothHilbertSheafQuotient

/-!
# The full quotient-defined presentation is effective in original fppf sheaves

The source uses its proved quotient-defined coefficient morphism. The full
original relation gives its coequalizer in sheaves, with no scheme effectivity claim.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertQuotientSheafCoequalizer
open HilbertChart CartierAbel SchemePicard FCurve
open OrderedHilbertIdentityQuotientOriginalSection
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
local notation "p" => OrderedHilbertQuotientFullRelation.fst f hL
local notation "q" => OrderedHilbertQuotientFullRelation.snd f hL

/-- The original Picard map from the exact quotient-defined relative scheme source. -/
def sourceMap : (Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.obj (quotientTest f hL)
    ⟶ smoothHilbertTargetSheaf f :=
  ⟨quotientMap f hL⟩

instance sourceMap_isLocallySurjective : Sheaf.IsLocallySurjective (sourceMap f hL) :=
  quotientMap_isLocallySurjective f hL

instance sourceMap_effectiveEpi : EffectiveEpi (sourceMap f hL) := by
  rw [← isRegularEpi_iff_effectiveEpi]
  exact IsRegularEpiCategory.regularEpiOfEpi _

/-- The entire old relation, including mixed components, is the sheaf kernel pair. -/
theorem isPullback :
    IsPullback ((Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map p)
        ((Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map q)
      (sourceMap f hL) (sourceMap f hL) := by
  apply IsPullback.of_map_of_faithful (sheafToPresheaf _ (Type 1))
  exact OrderedHilbertQuotientFullRelation.isPullback f hL

/-- The original Picard sheaf is the vertex of the full presentation cofork. -/
def cofork : Cofork ((Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map p)
    ((Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map q) :=
  Cofork.ofπ (sourceMap f hL) (isPullback f hL).w

/-- Effectivity here is proved in sheaves and retains the exact geometric source. -/
def isColimit : IsColimit (cofork f hL) :=
  isColimitCoforkOfEffectiveEpi (sourceMap f hL) _ (isPullback f hL).isLimit

/-- Maps from the original Picard sheaf are detected on this exact source. -/
theorem hom_ext {F : Sheaf (Scheme.fppfTopology.over (Spec (.of R))) (Type 1)} {a b :
    smoothHilbertTargetSheaf f ⟶ F}
    (h : sourceMap f hL ≫ a = sourceMap f hL ≫ b) : a = b :=
  (cancel_epi (sourceMap f hL)).mp h

end FLT.Mazur.OrderedHilbertQuotientSheafCoequalizer
