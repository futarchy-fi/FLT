/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationJointChartDomains
public import FLT.Mazur.EquivalenceRelationBoundaryChartTransport

/-!
# Original open coefficients on common overlaps of independent charts

The two independently restricted boundary coefficients agree on the entire
closed common-source overlap. The original section need only exist on its
invariant open, and neither frame needs to be complete.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
open InvariantBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B C : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J H : Type} [Fintype I] [Fintype J] [Fintype H] (o : I) (o' : J)
  (α : I ↪ H) (β : J ↪ H)
  (U : (source p q I o).Opens) (V : (source p q J o').Opens)
  (i : B ⟶ A) (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)
local notation "j" => InvariantBoundary.inclusion (p := p) (q := q) H (α o) i
local notation "j₁" => InvariantBoundary.inclusion (p := p) (q := q) I o i
local notation "j₂" => InvariantBoundary.inclusion (p := p) (q := q) J o' i
local notation "b₁" => endpoint (p := p) (q := q) I o i
local notation "b₂" => endpoint (p := p) (q := q) J o' i
local notation "W" => jointChartOpen e o o' α β U V

/-- The entire common boundary overlap identifies the two actual open-domain coefficients. -/
theorem jointChart_coefficient (E : B.Opens) (hE : r ⁻¹ᵁ E = s ⁻¹ᵁ E)
    (hU : (j₁) ⁻¹ᵁ U ≤ (b₁) ⁻¹ᵁ E) (hV : (j₂) ⁻¹ᵁ V ≤ (b₂) ⁻¹ᵁ E)
    (t : Γ(E.toScheme, ⊤)) (ht : (r ∣_ E).appTop t = (s.resLE E _ hE.le).appTop t) :
    (jointChartBoundaryFirst e o o' α β U V i z r s hr hs).appTop
        (((b₁).resLE E _ hU).appTop t) =
      (jointChartBoundarySecond e o o' α β U V i z r s hr hs).appTop
        (((b₂).resLE E _ hV).appTop t) := by
  have h₁ : (j) ⁻¹ᵁ W ≤
      subframeBoundaryMap e (α o) o i z r s hr hs α ⁻¹ᵁ ((j₁) ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, subframeBoundaryMap_inclusion,
      Scheme.Hom.comp_preimage]
    exact fun _ hx ↦ hx.1
  have h₂ : (j) ⁻¹ᵁ W ≤
      subframeBoundaryMap e (α o) o' i z r s hr hs β ⁻¹ᵁ ((j₂) ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, subframeBoundaryMap_inclusion,
      Scheme.Hom.comp_preimage]
    exact fun _ hx ↦ hx.2
  have hQ := subframeChart_domain e (α o) o α i z r s hr hs E hE
    ((j) ⁻¹ᵁ W) ((j₁) ⁻¹ᵁ U) h₁ hU
  exact (subframeChart_coefficient e (α o) o α i z r s hr hs E hE
    _ _ h₁ hU hQ t ht).trans
      (subframeChart_coefficient e (α o) o' β i z r s hr hs E hE
        _ _ h₂ hV hQ t ht).symm

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
