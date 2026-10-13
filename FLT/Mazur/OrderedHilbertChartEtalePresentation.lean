/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertBaseOpenImmersion
public import FLT.Mazur.OrderedHilbertChartFullEquivalence

/-!
# Actual etale geometry of the full original chart presentation

Etale translations give an etale source map and etale endpoints of the
entire original restricted relation. The relation endpoints are surjective
by their constructed reflexivity, without a quotient-scheme hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertBaseOpenChart
open HilbertChart CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))

/-- The whole constructed source intersection is etale over the original source. -/
instance inclusion_etale : Etale (inclusion f hL d V c).left := by
  have h := congrArg Over.Hom.left (toChartIntersection_inclusion f hL d V c)
  rw [← h]
  let _ : IsIso (toChartIntersection f hL d V c).left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso (chartIntersectionIso f hL d V c)).hom)
  change Etale ((toChartIntersection f hL d V c).left ≫
    (variableHilbertOverlapToTest f d V c
      (OrderedHilbertIdentityOriginalSection.sourceTest f hL)
      (OrderedHilbertIdentityOriginalSection.sourceSection f hL)).left)
  infer_instance

local notation "P" => OrderedHilbertIdentityOriginalRelation.fst f hL
local notation "Q" => OrderedHilbertIdentityOriginalRelation.snd f hL
local notation "j" => inclusion f hL d V c

local instance firstProjection_etale : Etale (pullback.fst P j).left :=
  MorphismProperty.of_isPullback ((IsPullback.of_hasPullback P j).map (Over.forget _)).flip
    (inferInstanceAs (Etale (j).left))

local instance secondProjection_etale : Etale (pullback.snd P j).left :=
  MorphismProperty.of_isPullback ((IsPullback.of_hasPullback P j).map (Over.forget _))
    (inferInstanceAs (Etale (P).left))

instance relationOther_etale : Etale (relationOther f hL d V c).left := by
  change Etale ((pullback.fst P j).left ≫ (Q).left)
  infer_instance

/-- The first endpoint of the full restricted relation is etale. -/
instance restrictedFst_etale : Etale (restrictedFst f hL d V c).left := by
  let _ : Etale (pullback.fst (relationOther f hL d V c) j).left :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback (relationOther f hL d V c) j).map (Over.forget _)).flip
      (inferInstanceAs (Etale (j).left))
  change Etale ((pullback.fst (relationOther f hL d V c) j).left ≫ (pullback.snd P j).left)
  infer_instance

/-- The independent second endpoint of the full restricted relation is etale. -/
instance restrictedSnd_etale : Etale (restrictedSnd f hL d V c).left :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback (relationOther f hL d V c) j).map (Over.forget _))
    (inferInstanceAs (Etale (relationOther f hL d V c).left))

omit [Etale V.hom] in
/-- Reflexivity covers the first endpoint of the original relation. -/
instance restrictedFst_surjective : Surjective (restrictedFst f hL d V c).left where
  surj x := ⟨(fullRestrictedEquivalence f hL d V c).r.left x,
    congrArg (fun k ↦ k.left x) (fullRestrictedEquivalence f hL d V c).reflexivity₁⟩

omit [Etale V.hom] in
/-- Reflexivity also covers the second endpoint, on the same full relation scheme. -/
instance restrictedSnd_surjective : Surjective (restrictedSnd f hL d V c).left where
  surj x := ⟨(fullRestrictedEquivalence f hL d V c).r.left x,
    congrArg (fun k ↦ k.left x) (fullRestrictedEquivalence f hL d V c).reflexivity₂⟩

end FLT.Mazur.OrderedHilbertBaseOpenChart
