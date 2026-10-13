/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertQuotientSchemeDescent
public import FLT.Mazur.RelativeFppfRepresentedCover

/-!
# A geometric effectivity criterion for the full original presentation

An actual relative fppf morphism from the constructed source, with the FULL
original relation as scheme kernel pair, gives representation of the original
Picard sheaf. These geometric inputs are hypotheses, not constructed here.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertQuotientSchemeCriterion
open HilbertChart CartierAbel SchemePicard FCurve
open OrderedHilbertIdentityQuotientOriginalSection OrderedHilbertQuotientSheafCoequalizer
open OrderedHilbertQuotientSchemeDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
local notation "p" => OrderedHilbertQuotientFullRelation.fst f hL
local notation "q" => OrderedHilbertQuotientFullRelation.snd f hL
variable {Z : Over (Spec (.of R))} (a : quotientTest f hL ⟶ Z)
  [Flat a.left] [Surjective a.left] [LocallyOfFinitePresentation a.left]
  (H : IsPullback (OrderedHilbertQuotientFullRelation.fst f hL)
    (OrderedHilbertQuotientFullRelation.snd f hL) a a)

/-- The actual fppf scheme projection gives a sheaf effective epimorphism. -/
theorem target_effectiveEpi : EffectiveEpi
    ((Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map a) := by
  let _ := RelativeFppfRepresentedCover.sheaf_isLocallySurjective a
  rw [← isRegularEpi_iff_effectiveEpi]
  exact IsRegularEpiCategory.regularEpiOfEpi _

/-- Geometric effectivity identifies the represented target as the full sheaf coequalizer. -/
def targetIsColimit : IsColimit (targetCofork f hL a H.w) := by
  let _ := target_effectiveEpi f hL a
  have h : IsPullback ((Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map p)
      ((Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map q)
      ((Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map a)
      ((Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map a) := by
    apply IsPullback.of_map_of_faithful (sheafToPresheaf _ (Type 1))
    exact H.map uliftYoneda.{1}
  exact isColimitCoforkOfEffectiveEpi
    ((Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map a) _ h.isLimit

/-- The resulting representation is of the ORIGINAL fppf sheaf on all relative tests. -/
def representation : smoothHilbertTargetSheaf f ≅
    (Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.obj Z :=
  (isColimit f hL).coconePointUniqueUpToIso (targetIsColimit f hL a H)

/-- The representation map is the previously constructed descent of the actual scheme map. -/
theorem representation_hom : (representation f hL a H).hom = descend f hL a H.w := rfl

/-- The representation recovers the prescribed geometric source projection. -/
@[reassoc]
theorem source_representation :
    sourceMap f hL ≫ (representation f hL a H).hom =
      (Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map a :=
  source_descend f hL a H.w

/-- Its inverse retains precisely the original Picard map on the exact source. -/
theorem representation_inv_source :
    (Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map a ≫
      (representation f hL a H).inv = sourceMap f hL := by
  rw [← source_representation f hL a H, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.OrderedHilbertQuotientSchemeCriterion
