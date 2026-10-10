/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricallyConnectedLocus
public import FLT.Mazur.PointedFieldGeometricConnectedness
public import FLT.Mazur.SmoothGeometricallyReduced

/-!
# The connected fiber locus as an evaluation-injectivity locus

For a proper reduced pointed scheme over a field, evaluation at the section
is injective exactly when the scheme is geometrically connected. Applied to
the actual residue-field fibers of a proper smooth family, this identifies
the geometric locus with a concrete locus of injective ring maps.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open FLT.Mazur.FCurve

/-- Evaluation detects geometric connectedness on a proper reduced pointed field scheme. -/
theorem geometricallyConnected_iff_sectionEvaluation_injective {K : Type} [Field K]
    {X : Scheme} (f : X ⟶ Spec (.of K)) [IsProper f] [IsReduced X]
    (s : Spec (.of K) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    GeometricallyConnected f ↔ Function.Injective (sectionEvaluation s) := by
  constructor
  · intro h
    have : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton f
    let _ := (globalSections_isField_of_proper_connected_reduced f).toField
    exact (sectionEvaluation s).injective
  · intro h
    have : Nonempty X := ⟨s (Classical.arbitrary (Spec (.of K)))⟩
    have : ConnectedSpace X :=
      connectedSpace_of_injective_global_evaluation X (sectionEvaluation s) h
    exact geometricallyConnected_of_proper_connected_reduced_section f s hs

/-- The original section base changed to the actual residue-field fiber. -/
def residueFiberSection {X S : Scheme} (f : X ⟶ S) (s : S ⟶ X)
    (hs : s ≫ f = 𝟙 S) (b : S) : Spec (S.residueField b) ⟶ f.fiber b :=
  pullback.lift (S.fromSpecResidueField b ≫ s) (𝟙 _) (by simp [hs])

/-- The actual fiber section retracts its structure morphism. -/
theorem residueFiberSection_projection {X S : Scheme} (f : X ⟶ S) (s : S ⟶ X)
    (hs : s ≫ f = 𝟙 S) (b : S) :
    residueFiberSection f s hs b ≫ f.fiberToSpecResidueField b = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- For reduced proper fibers, membership is injectivity of their actual section evaluation. -/
theorem mem_geometricallyConnectedLocus_iff_evaluation {X S : Scheme}
    (f : X ⟶ S) [IsProper f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    (b : S) [IsReduced (f.fiber b)] :
    b ∈ geometricallyConnectedLocus f ↔
      Function.Injective (sectionEvaluation (residueFiberSection f s hs b)) := by
  have : IsProper (f.fiberToSpecResidueField b) :=
    inferInstanceAs (IsProper (pullback.snd f (S.fromSpecResidueField b)))
  exact geometricallyConnected_iff_sectionEvaluation_injective (f.fiberToSpecResidueField b)
    (residueFiberSection f s hs b) (residueFiberSection_projection f s hs b)

/-- Smoothness supplies reduced fibers, so the locus is exactly the evaluation-injectivity set. -/
theorem geometricallyConnectedLocus_eq_evaluation_locus_of_smooth {X S : Scheme}
    (f : X ⟶ S) [IsProper f] [Smooth f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) :
    geometricallyConnectedLocus f =
      {b | Function.Injective (sectionEvaluation (residueFiberSection f s hs b))} := by
  ext b
  have : Smooth (f.fiberToSpecResidueField b) :=
    inferInstanceAs (Smooth (pullback.snd f (S.fromSpecResidueField b)))
  have : IsReduced (f.fiber b) := isReduced_of_smooth_field (f.fiberToSpecResidueField b)
  exact mem_geometricallyConnectedLocus_iff_evaluation f s hs b

end FLT.Mazur.Approximation
