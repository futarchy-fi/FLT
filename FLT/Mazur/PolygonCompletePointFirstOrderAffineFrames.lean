/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstOrderOpen
public import FLT.Mazur.DivisorFrameIdeal

/-!
# Actual Cartier frames inside the original first-order neighborhood

Every point of the first-order neighborhood has an affine Cartier chart inside it.
On each such chart the canonical section generates the full original marking ideal
in every linear frame, retaining the original ideal's multiplicity.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor completeBaseMarking Scheme.Hom.ker

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "s" => completeBaseMarking K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)
local notation "D" => divisorLineBundle (Scheme.Hom.ker (s)) hI

/-- The original marking ideal on a Cartier chart is its canonical section's full ideal. -/
theorem completePointMarkingIdeal_frame (U : (exactVeroneseProj K n h).affineOpens)
    (hU : CartierChart (s).ker U)
    (e : Γ((D), U.1) ≃ₗ[Γ(exactVeroneseProj K n h, U.1)]
      Γ(exactVeroneseProj K n h, U.1)) :
    Ideal.span {e (divisorSection hI U.1)} = (s).ker.ideal U :=
  divisorSection_span_in_frame hI hU e

/-- Actual affine frames can be chosen inside the first-order neighborhood at every point. -/
theorem completePointFirstOrder_affineFrame (x : exactVeroneseProj K n h)
    (hx : x ∈ completePointFirstOrderOpen K n h i) :
    ∃ (U : (exactVeroneseProj K n h).affineOpens), x ∈ U.1 ∧
      U.1 ≤ completePointFirstOrderOpen K n h i ∧ CartierChart (s).ker U ∧
      ∃ e : Γ((D), U.1) ≃ₗ[Γ(exactVeroneseProj K n h, U.1)]
        Γ(exactVeroneseProj K n h, U.1),
        Ideal.span {e (divisorSection hI U.1)} = (s).ker.ideal U := by
  obtain ⟨U, hxU, hU, hC⟩ := (hI).exists_chart_le hx
  refine ⟨U, hxU, hU, hC, (hC.divisorSectionsEquiv hI).trans hC.dualEquiv, ?_⟩
  exact completePointMarkingIdeal_frame K n h i U hC _

end FLT.Mazur.PolygonInfinitesimalStages
