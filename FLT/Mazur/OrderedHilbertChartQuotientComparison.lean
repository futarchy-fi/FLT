/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertChartRelationCover
public import FLT.Mazur.RelativeRelationFppfRefinement

/-!
# The entire original restricted quotient on every translated chart

The constructed source and relation covers identify the full original
restricted locally ringed coequalizer with the full parameter quotient.
This holds for arbitrary translations, without an open-base hypothesis,
and preserves all regular functions and the original coefficient morphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertBaseOpenChart
open HilbertChart CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "P₁" => restrictedFst f hL d V c
local notation "P₂" => restrictedSnd f hL d V c
local notation "Q₁" => variableChartRelationFst f hL d V c
local notation "Q₂" => variableChartRelationSnd f hL d V c
local notation "g" => projection f hL d V c
local notation "e" => variableChartEquivalenceRelation f hL d V c

/-- Equal parameters imply equal original classes on the actual scheme kernel pair. -/
theorem full_kernel_class :
    (relativeFppfSheaf f).obj.map
      (pullback.fst g g ≫ inclusion f hL d V c).op
        (OrderedHilbertIdentityOriginalSection.sourceSection f hL) =
    (relativeFppfSheaf f).obj.map
      (pullback.snd g g ≫ inclusion f hL d V c).op
        (OrderedHilbertIdentityOriginalSection.sourceSection f hL) := by
  rw [full_parameter_class, full_parameter_class, pullback.condition]

/-- The parameter kernel pair maps into the entire original restricted relation. -/
def fullKernelToRelation : pullback g g ⟶ restrictedRelation f hL d V c :=
  (full_restricted_lift f hL d V c _ _ (full_kernel_class f hL d V c)).choose

@[reassoc]
theorem fullKernelToRelation_fst :
    fullKernelToRelation f hL d V c ≫ P₁ = pullback.fst g g :=
  (full_restricted_lift f hL d V c _ _ (full_kernel_class f hL d V c)).choose_spec.1.1

@[reassoc]
theorem fullKernelToRelation_snd :
    fullKernelToRelation f hL d V c ≫ P₂ = pullback.snd g g :=
  (full_restricted_lift f hL d V c _ _ (full_kernel_class f hL d V c)).choose_spec.1.2

/-- Full locally ringed effectivity transfers across the constructed source and relation covers. -/
def fullChartQuotientIso : locallyRingedQuotient (p := P₁) (q := P₂) ≅
    locallyRingedQuotient (p := Q₁) (q := Q₂) :=
  RelativeRelationFppfRefinement.quotientIso P₁ P₂ Q₁ Q₂ g
    (fullRelationToChart f hL d V c) (fullRelationToChart_fst f hL d V c)
    (fullRelationToChart_snd f hL d V c) (fullKernelToRelation f hL d V c)
    (fullKernelToRelation_fst f hL d V c) (fullKernelToRelation_snd f hL d V c)

/-- The comparison recovers the original geometric parameter map on the full source. -/
@[reassoc]
theorem fullChartQuotientIso_source :
    locallyRingedProjection (p := P₁) (q := P₂) ≫
      (fullChartQuotientIso f hL d V c).hom =
        (g).left.toLRSHom ≫ locallyRingedProjection (p := Q₁) (q := Q₂) :=
  RelativeRelationFppfRefinement.quotientIso_source _ _ _ _ _ _ _ _ _ _ _

/-- The comparison preserves the exact original coefficient map. -/
theorem fullChartQuotientIso_base :
    (fullChartQuotientIso f hL d V c).hom ≫ locallyRingedBaseMap (p := Q₁) (q := Q₂) =
      locallyRingedBaseMap (p := P₁) (q := P₂) :=
  RelativeRelationFppfRefinement.quotientIso_base _ _ _ _ _ _ _ _ _ _ _

/-- All invariant regular functions on the full chart model the original restricted quotient. -/
def fullChartInvariantIso : locallyRingedQuotient (p := P₁) (q := P₂) ≅
    invariantLocallyRingedSpace e :=
  fullChartQuotientIso f hL d V c ≪≫ invariantLocallyRingedIso e

/-- The invariant comparison has the actual full-source parameter map as projection. -/
@[reassoc]
theorem fullChartInvariantIso_source :
    locallyRingedProjection (p := P₁) (q := P₂) ≫
      (fullChartInvariantIso f hL d V c).hom =
        (g).left.toLRSHom ≫ invariantLocallyRingedProjection e := by
  dsimp only [fullChartInvariantIso, Iso.trans_hom, invariantLocallyRingedProjection]
  rw [fullChartQuotientIso_source_assoc]

/-- Invariant functions and coefficient morphisms are preserved together. -/
theorem fullChartInvariantIso_base :
    (fullChartInvariantIso f hL d V c).hom ≫ invariantLocallyRingedBaseMap e =
      locallyRingedBaseMap (p := P₁) (q := P₂) := by
  dsimp only [fullChartInvariantIso, Iso.trans_hom, invariantLocallyRingedBaseMap]
  rw [Category.assoc, Iso.hom_inv_id_assoc, fullChartQuotientIso_base]

end FLT.Mazur.OrderedHilbertBaseOpenChart
