/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperDenseOpenIso
public import FLT.Mazur.SmoothCurveValuationStalk

/-!
# Recognizing a map of smooth field curves from a common open

An existing map from a proper integral curve to a smooth integral separated
curve is an isomorphism if it identifies a nonempty open in both curves.
The inverse is constructed using valuation stalks only over the field.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve

universe u

/-- A nonempty common open detects the original morphism of smooth field curves. -/
theorem smoothCurve_isIso_of_commonOpen {K : Type u} [Field K]
    {X Y U : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [Nonempty U]
    (q : X ⟶ Spec (.of K)) (r : Y ⟶ Spec (.of K))
    [IsProper q] [IsSeparated r] [SmoothOfRelativeDimension 1 r]
    (j : U ⟶ X) [IsOpenImmersion j] (k : U ⟶ Y) [IsOpenImmersion k]
    (f : X ⟶ Y) (hf : f ≫ r = q) (hjk : j ≫ f = k) : IsIso f := by
  let _ : X.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← Limits.terminal.comp_from q]
    infer_instance
  let _ : Y.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← Limits.terminal.comp_from r]
    infer_instance
  let _ : ∀ y : Y, ValuationRing (Y.presheaf.stalk y) :=
    fun y ↦ smoothCurve_stalk_valuationRing r y
  let _ : IsDominant j := ⟨j.isOpenMap.isOpen_range.dense (Set.range_nonempty j)⟩
  let _ : IsDominant k := ⟨k.isOpenMap.isOpen_range.dense (Set.range_nonempty k)⟩
  exact isIso_of_common_denseOpen q r j k f hf hjk

end FLT.Mazur.FCurve
