/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConnectedOfGlobalSections
public import FLT.Mazur.FlatGlobalFunctionsPushout
public import FLT.Mazur.ProperConnectedReducedSections

/-!
# Global-function criteria for pointed proper fibers

Constant global functions imply geometric connectedness because they remain
constant after every field extension. For a proper reduced scheme with a
rational point, connectedness, geometric connectedness, and constant global
functions are therefore equivalent. No geometric reducedness is required.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open FLT.Mazur.FCurve

/-- An actual scalar isomorphism detects geometric connectedness of a pointed qcqs scheme. -/
theorem geometricallyConnected_of_field_appTop_iso {K : Type} [Field K]
    {X : Scheme} [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of K)) (s : Spec (.of K) ⟶ X) (hs : s ≫ f = 𝟙 _)
    [IsIso f.appTop] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun L _ y ↦ ?_⟩
  let q := pullback.snd f y
  have : IsIso q.appTop := isIso_appTop_of_flat_cartesian (IsPullback.of_hasPullback f y)
  have : IsDomain Γ(pullback f y, ⊤) :=
    (asIso q.appTop).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  have := preconnectedSpace_of_globalSections_domain (pullback f y)
  let t : Spec (.of L) ⟶ pullback f y :=
    pullback.lift (y ≫ s) (𝟙 _) (by simp [hs])
  exact ⟨⟨t (Classical.arbitrary (Spec (.of L)))⟩⟩

/-- Constant global functions detect geometric connectedness for a pointed proper scheme. -/
theorem geometricallyConnected_of_constantGlobalSections {K : Type} [Field K]
    {X : Scheme} (f : X ⟶ Spec (.of K)) [IsProper f]
    (s : Spec (.of K) ⟶ X) (hs : s ≫ f = 𝟙 _) (hf : HasConstantGlobalSections f) :
    GeometricallyConnected f := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have hi : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hf
  have : IsIso f.appTop := by rwa [isIso_comp_left_iff] at hi
  exact geometricallyConnected_of_field_appTop_iso f s hs

/-- A connected proper reduced scheme with a rational point is geometrically connected. -/
theorem geometricallyConnected_of_proper_connected_reduced_section {K : Type} [Field K]
    {X : Scheme} (f : X ⟶ Spec (.of K)) [IsProper f] [IsReduced X] [ConnectedSpace X]
    (s : Spec (.of K) ⟶ X) (hs : s ≫ f = 𝟙 _) : GeometricallyConnected f :=
  geometricallyConnected_of_constantGlobalSections f s hs
    (constantGlobalSections_of_proper_connected_reduced_section f s hs)

/-- Proper reduced pointed schemes are geometrically connected exactly when they are connected. -/
theorem geometricallyConnected_iff_connected_of_proper_reduced_section {K : Type} [Field K]
    {X : Scheme} (f : X ⟶ Spec (.of K)) [IsProper f] [IsReduced X]
    (s : Spec (.of K) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    GeometricallyConnected f ↔ ConnectedSpace X := by
  constructor
  · intro h
    exact GeometricallyConnected.connectedSpace_of_subsingleton f
  · intro h
    exact geometricallyConnected_of_proper_connected_reduced_section f s hs

end FLT.Mazur.Approximation
