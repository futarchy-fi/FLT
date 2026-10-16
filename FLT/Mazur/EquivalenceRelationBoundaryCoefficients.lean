/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryActionGeometry
public import FLT.Mazur.FiniteGroupEquivariantOpenBoundary

/-!
# Original closed relation coefficients on moving affine tests

An original boundary function equalized by the entire closed relation induces
an invariant function for the moving normalized action. On every stable affine
source open, this exact function has an invariant lift and a finite certificate.
The source-open existence and descent back to the original relation are separate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
open SchemeFiniteGroupQuotient FiniteGroupRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B C : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (i : B ⟶ A) [Mono i] (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)
local notation "ρ" => action e I o i z r s hr hs
local notation "τ" => EquivalenceRelationNormalizedFrames.action e I o
local notation "j" => inclusion (p := p) (q := q) I o i
local notation "b" => endpoint (p := p) (q := q) I o i
variable (t : Γ(B, ⊤)) (ht : r.appTop t = s.appTop t)

include ht in
/-- Pulling an original equalized function to the exact boundary preserves the moving action. -/
theorem endpoint_coefficient_invariant (σ : Equiv.Perm I) :
    (ρ σ).hom.appTop ((b).appTop t) = (b).appTop t := by
  change (((b).appTop ≫ (ρ σ).hom.appTop) t) = _
  rw [← Scheme.Hom.comp_appTop]
  change (map e I o i z r s hr hs σ ≫ b).appTop t = _
  rw [map_endpoint, Scheme.Hom.comp_appTop]
  change (transition I o i z r hr σ).appTop (s.appTop t) = _
  rw [← ht]
  change ((r.appTop ≫ (transition I o i z r hr σ).appTop) t) = _
  rw [← Scheme.Hom.comp_appTop, transition_first]

/-- The invariant normalized boundary coefficient constructed from the original whole relation. -/
def invariantCoefficient : invariantCoordinates ρ := by
  let _ := SchemeCoordinateAction.coordinateAction ρ
  refine ⟨(b).appTop t, ?_⟩
  intro σ
  exact endpoint_coefficient_invariant e I o i z r s hr hs t ht σ⁻¹

/-- The underlying coefficient is exactly restriction from the original closed endpoint. -/
theorem invariantCoefficient_val :
    (invariantCoefficient e I o i z r s hr hs t ht).val = (b).appTop t := rfl

variable (U : (source p q I o).Opens)
  (hU : ∀ σ : Equiv.Perm I,
    (EquivalenceRelationNormalizedFrames.action e I o σ).hom ⁻¹ᵁ U = U)
local notation "hj" => action_inclusion e I o i z r s hr hs
local notation "ρU" => boundaryOpenAction ρ τ j hj U hU
local notation "τU" => restrictedAction τ U hU
local notation "hι" => boundaryOpen_equivariant ρ τ j hj U hU

/-- The exact original boundary coefficient on the chosen stable source open. -/
def openInvariantCoefficient : invariantCoordinates ρU :=
  invariantMap ρU ρ (j ⁻¹ᵁ U).ι
    (restrictedAction_hom_ι ρ (j ⁻¹ᵁ U) (boundaryOpen_stable ρ τ j hj U hU))
    (invariantCoefficient e I o i z r s hr hs t ht)

/-- The chart coefficient uses the original scheme restriction, retaining nilpotents. -/
theorem openInvariantCoefficient_val :
    (openInvariantCoefficient e I o i z r s hr hs t ht U hU).val =
      ((j ⁻¹ᵁ U).ι ≫ b).appTop t := rfl

variable [IsClosedImmersion i]

/-- Every whole-relation boundary coefficient lifts invariantly on a stable affine source test. -/
theorem openInvariantCoefficient_lift (ha : IsAffineOpen U) :
    ∃ a : invariantCoordinates τU,
      invariantMap ρU τU (j ∣_ U) hι a =
        openInvariantCoefficient e I o i z r s hr hs t ht U hU :=
  boundaryOpen_invariantMap_surjective ρ τ j hj U hU
    (fun _ _ a σ h ↦ EquivalenceRelationNormalizedFrames.action_free e I o a σ h) ha _

/-- The actual original coefficient has a finite identity on every such affine chart. -/
theorem openInvariantCoefficient_certificate (ha : IsAffineOpen U) :
    ∃ a : sectionLiftIdeal (invariantMap ρU τU (j ∣_ U) hι)
        (openInvariantCoefficient e I o i z r s hr hs t ht U hU) →₀ Γ((j ⁻¹ᵁ U).toScheme, ⊤),
      a.sum (fun v coeff ↦ coeff * (invariantMap ρU τU (j ∣_ U) hι v.val).val) = 1 :=
  boundaryOpen_certificate ρ τ j hj U hU
    (fun _ _ a σ h ↦ EquivalenceRelationNormalizedFrames.action_free e I o a σ h) ha _

end FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
