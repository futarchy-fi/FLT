/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryActionGeometry
public import FLT.Mazur.FiniteGroupOpenRelationCoefficients

/-!
# Arbitrary original open boundary sections on moving affine charts

Every function equalized by the entire original closed relation over its open
domain has an exact invariant coefficient on any moving chart above that domain.
On an affine source chart the coefficient lifts and has a finite identity.
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
local notation "hj" => action_inclusion e I o i z r s hr hs
variable (V : B.Opens) (hV : r ⁻¹ᵁ V = s ⁻¹ᵁ V)
  (U : (source p q I o).Opens)
  (hU : ∀ σ : Equiv.Perm I,
    (EquivalenceRelationNormalizedFrames.action e I o σ).hom ⁻¹ᵁ U = U)
  (hUV : inclusion (p := p) (q := q) I o i ⁻¹ᵁ U ≤ endpoint I o i ⁻¹ᵁ V)
  (t : Γ(V.toScheme, ⊤))
  (ht : (r ∣_ V).appTop t = (s.resLE V _ hV.le).appTop t)
local notation "ρU" => boundaryOpenAction ρ τ j hj U hU
local notation "τU" => restrictedAction τ U hU
local notation "hι" => boundaryOpen_equivariant ρ τ j hj U hU

/-- The exact coefficient of an original section that exists only on its invariant open. -/
def domainInvariantCoefficient : invariantCoordinates ρU :=
  FiniteGroupOpenRelation.invariantCoefficient ρ b r s (transition I o i z r hr)
    (transition_first I o i z r hr)
    (fun σ ↦ (map_endpoint e I o i z r s hr hs σ).symm) V hV (j ⁻¹ᵁ U)
    (boundaryOpen_stable ρ τ j hj U hU) hUV t ht

/-- The coefficient is the original open section pulled back along the actual closed endpoint. -/
theorem domainInvariantCoefficient_val :
    (domainInvariantCoefficient e I o i z r s hr hs V hV U hU hUV t ht).val =
      ((b).resLE V (j ⁻¹ᵁ U) hUV).appTop t := rfl

variable [IsClosedImmersion i]

/-- Arbitrary original open-domain coefficients lift on the moving affine source chart. -/
theorem domainInvariantCoefficient_lift (ha : IsAffineOpen U) :
    ∃ a : invariantCoordinates τU, invariantMap ρU τU (j ∣_ U) hι a =
      domainInvariantCoefficient e I o i z r s hr hs V hV U hU hUV t ht :=
  boundaryOpen_invariantMap_surjective ρ τ j hj U hU
    (fun _ _ a σ h ↦ EquivalenceRelationNormalizedFrames.action_free e I o a σ h) ha _

/-- The finite chart identity applies to every section on the original invariant domain. -/
theorem domainInvariantCoefficient_certificate (ha : IsAffineOpen U) :
    ∃ a : sectionLiftIdeal (invariantMap ρU τU (j ∣_ U) hι)
        (domainInvariantCoefficient e I o i z r s hr hs V hV U hU hUV t ht) →₀
          Γ((j ⁻¹ᵁ U).toScheme, ⊤),
      a.sum (fun v coeff ↦ coeff * (invariantMap ρU τU (j ∣_ U) hι v.val).val) = 1 :=
  boundaryOpen_certificate ρ τ j hj U hU
    (fun _ _ a σ h ↦ EquivalenceRelationNormalizedFrames.action_free e I o a σ h) ha _

end FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
