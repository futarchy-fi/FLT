/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierCharts
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Finite presentation of an effective Cartier immersion

Locally the closed immersion is the quotient by one regular equation. Its kernel
is therefore finitely generated, without any Noetherian assumption on the base.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve

variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- An effective Cartier divisor is locally of finite presentation in its ambient scheme. -/
theorem EffectiveCartier.locallyOfFinitePresentation_subschemeι (hI : EffectiveCartier I) :
    LocallyOfFinitePresentation I.subschemeι := by
  apply (HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
    (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finitePresentation_holdsForLocalizationAway).left).mpr
  intro x
  obtain ⟨U, hx, hU⟩ := hI (I.subschemeι x)
  refine ⟨U, ⟨I.subschemeι ⁻¹ᵁ U, U.2.preimage I.subschemeι⟩, hx, le_rfl, ?_⟩
  rw [Scheme.Hom.appLE_eq_app]
  apply RingHom.FinitePresentation.of_surjective _ (I.subschemeι.app_surjective U U.2)
  obtain ⟨a, _, ha⟩ := CartierChart.ker_eq hU
  rw [ha]
  exact Submodule.fg_span_singleton a

/-- The structural morphism of a Cartier divisor in a finitely presented family is
locally of finite presentation. -/
theorem EffectiveCartier.locallyOfFinitePresentation_comp {S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (hI : EffectiveCartier I) :
    LocallyOfFinitePresentation (I.subschemeι ≫ f) := by
  let _ := hI.locallyOfFinitePresentation_subschemeι
  infer_instance

end FLT.Mazur.FCurve
