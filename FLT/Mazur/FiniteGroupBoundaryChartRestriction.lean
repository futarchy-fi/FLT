/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupOpenCoefficientRefinement

/-!
# Boundary chart maps commute with actual source refinement

The source invariant ring, the exact boundary invariant ring, and their
restriction maps form a commuting square. Consequently any chosen invariant
lift on a chart restricts to a lift on every smaller stable source chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteGroupRestriction
open SchemeFiniteGroupQuotient FiniteGroupOpenRelation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type} [Group G] {X Y : Scheme}
  (ρ : G →* Aut X) (τ : G →* Aut Y) (i : X ⟶ Y)
  (hi : ∀ g : G, (ρ g).hom ≫ i = i ≫ (τ g).hom)
  (U : Y.Opens) (hU : ∀ g : G, (τ g).hom ⁻¹ᵁ U = U)
  (V : Y.Opens) (hV : ∀ g : G, (τ g).hom ⁻¹ᵁ V = V) (h : V ≤ U)
local notation "ρU" => boundaryOpenAction ρ τ i hi U hU
local notation "ρV" => boundaryOpenAction ρ τ i hi V hV
local notation "τU" => restrictedAction τ U hU
local notation "τV" => restrictedAction τ V hV
local notation "mU" => invariantMap ρU τU (i ∣_ U) (boundaryOpen_equivariant ρ τ i hi U hU)
local notation "mV" => invariantMap ρV τV (i ∣_ V) (boundaryOpen_equivariant ρ τ i hi V hV)

/-- Restrict invariant coordinates on the unchanged inverse-image boundary. -/
def boundaryInvariantRestriction : invariantCoordinates ρU →+* invariantCoordinates ρV :=
  invariantRestriction ρ (i ⁻¹ᵁ U) (boundaryOpen_stable ρ τ i hi U hU)
    (i ⁻¹ᵁ V) (boundaryOpen_stable ρ τ i hi V hV) (i.preimage_mono h)

/-- Refinement uses the exact boundary open immersion on underlying coefficients. -/
theorem boundaryInvariantRestriction_val (t : invariantCoordinates ρU) :
    (boundaryInvariantRestriction ρ τ i hi U hU V hV h t).val =
      (X.homOfLE (i.preimage_mono h)).appTop t.val := rfl

/-- The original closed chart map commutes with both actual source restrictions. -/
theorem boundary_chart_restriction (a : invariantCoordinates τU) :
    boundaryInvariantRestriction ρ τ i hi U hU V hV h (mU a) =
      mV (invariantRestriction τ U hU V hV h a) := by
  apply Subtype.ext
  simp only [boundaryInvariantRestriction_val, invariantRestriction_val, invariantMap_val]
  change (((i ∣_ U).appTop ≫ (X.homOfLE (i.preimage_mono h)).appTop) a.val) =
    (((Y.homOfLE h).appTop ≫ (i ∣_ V).appTop) a.val)
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, morphismRestrict_homOfLE]

/-- Every invariant lift stays a lift under any stable source refinement. -/
theorem boundary_chart_lift_restriction (a : invariantCoordinates τU)
    (t : invariantCoordinates ρU) (ha : mU a = t) :
    mV (invariantRestriction τ U hU V hV h a) =
      boundaryInvariantRestriction ρ τ i hi U hU V hV h t := by
  rw [← ha, boundary_chart_restriction]

end FLT.Mazur.FiniteGroupRestriction
