/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertQuotientSheafCoequalizer

/-!
# Descent into arbitrary relative schemes from the full original presentation

A scheme map constant on the full relation descends uniquely to a map from
the ORIGINAL Picard sheaf into the represented target. This constructs maps;
it does not assume the Picard sheaf itself has a representing scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertQuotientSchemeDescent
open HilbertChart CartierAbel SchemePicard FCurve
open OrderedHilbertIdentityQuotientOriginalSection OrderedHilbertQuotientSheafCoequalizer
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
local notation "p" => OrderedHilbertQuotientFullRelation.fst f hL
local notation "q" => OrderedHilbertQuotientFullRelation.snd f hL
variable {Z : Over (Spec (.of R))} (a : quotientTest f hL ⟶ Z)
  (ha : OrderedHilbertQuotientFullRelation.fst f hL ≫ a =
    OrderedHilbertQuotientFullRelation.snd f hL ≫ a)

/-- The target scheme map defines a cofork for the ENTIRE original relation. -/
def targetCofork : Cofork ((Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map p)
    ((Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map q) :=
  Cofork.ofπ ((Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map a) (by
    rw [← Functor.map_comp, ← Functor.map_comp, ha])

/-- Actual descent of the compatible source map to the original Picard sheaf. -/
def descend : smoothHilbertTargetSheaf f ⟶
    (Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.obj Z :=
  (isColimit f hL).desc (targetCofork f hL a ha)

/-- The constructed map recovers the prescribed source morphism exactly. -/
@[reassoc]
theorem source_descend : sourceMap f hL ≫ descend f hL a ha =
    (Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map a :=
  Cofork.IsColimit.π_desc (isColimit f hL)

/-- Every such descended map is unique on all relative tests. -/
theorem descend_unique (b : smoothHilbertTargetSheaf f ⟶
    (Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.obj Z)
    (hb : sourceMap f hL ≫ b = (Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map a) :
        b = descend f hL a ha :=
  OrderedHilbertQuotientSheafCoequalizer.hom_ext f hL
    (hb.trans (source_descend f hL a ha).symm)

/-- Descent commutes with every actual relative target morphism. -/
theorem descend_comp {Z' : Over (Spec (.of R))} (b : Z ⟶ Z') :
    descend f hL a ha ≫ (Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map b =
      descend f hL (a ≫ b) (by rw [← Category.assoc, ha, Category.assoc]) := by
  apply descend_unique
  rw [source_descend_assoc, ← Functor.map_comp]

/-- The source morphism attached to any map from the original Picard sheaf. -/
def sourceMorphism (b : smoothHilbertTargetSheaf f ⟶
    (Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.obj Z) :
    quotientTest f hL ⟶ Z :=
  (Scheme.fppfTopology.over (Spec (.of R))).fullyFaithfulUliftYoneda.preimage (sourceMap f hL ≫ b)

/-- The extracted morphism is compatible on the full original scheme relation. -/
theorem sourceMorphism_condition
    (b : smoothHilbertTargetSheaf f ⟶
        (Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.obj Z) :
    p ≫ sourceMorphism f hL b = q ≫ sourceMorphism f hL b := by
  apply (Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map_injective
  simp only [Functor.map_comp, sourceMorphism,
    Functor.FullyFaithful.map_preimage, ← Category.assoc]
  rw [(OrderedHilbertQuotientSheafCoequalizer.isPullback f hL).w]

/-- Extracting a source morphism after descent recovers the original scheme map. -/
theorem sourceMorphism_descend : sourceMorphism f hL (descend f hL a ha) = a := by
  apply (Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.map_injective
  rw [sourceMorphism, Functor.FullyFaithful.map_preimage, source_descend]

/-- Descent recovers the original map on ALL relative tests after source extraction. -/
theorem descend_sourceMorphism
    (b : smoothHilbertTargetSheaf f ⟶
        (Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.obj Z) :
    descend f hL (sourceMorphism f hL b) (sourceMorphism_condition f hL b) = b := by
  symm
  apply descend_unique
  exact ((Scheme.fppfTopology.over (Spec (.of R))).fullyFaithfulUliftYoneda.map_preimage _).symm

end FLT.Mazur.OrderedHilbertQuotientSchemeDescent
