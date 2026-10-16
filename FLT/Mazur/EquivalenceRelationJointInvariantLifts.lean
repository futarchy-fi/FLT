/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationJointChartLiftDifference
public import FLT.Mazur.EquivalenceRelationBoundaryOpenCoefficients

/-!
# Constructed invariant lifts and their exact common-boundary compatibility

On two independent stable affine charts, freeness constructs invariant lifts
of every original open boundary section. Their pullbacks agree on the entire
common boundary and their discrepancy lies in its exact kernel ideal.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
open InvariantBoundary SchemeFiniteGroupQuotient FiniteGroupRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B C : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J H : Type} [Fintype I] [Fintype J] [Fintype H] (o : I) (o' : J)
  (α : I ↪ H) (β : J ↪ H)
  (U : (source p q I o).Opens) (V : (source p q J o').Opens)
  (hU : ∀ σ : Equiv.Perm I,
    (EquivalenceRelationNormalizedFrames.action e I o σ).hom ⁻¹ᵁ U = U)
  (hV : ∀ σ : Equiv.Perm J,
    (EquivalenceRelationNormalizedFrames.action e J o' σ).hom ⁻¹ᵁ V = V)
  (i : B ⟶ A) [IsClosedImmersion i] (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)
local notation "j" => InvariantBoundary.inclusion (p := p) (q := q) H (α o) i
local notation "j₁" => InvariantBoundary.inclusion (p := p) (q := q) I o i
local notation "j₂" => InvariantBoundary.inclusion (p := p) (q := q) J o' i
local notation "b₁" => endpoint (p := p) (q := q) I o i
local notation "b₂" => endpoint (p := p) (q := q) J o' i
local notation "W" => jointChartOpen e o o' α β U V
local notation "τ₁" => EquivalenceRelationNormalizedFrames.action e I o
local notation "τ₂" => EquivalenceRelationNormalizedFrames.action e J o'

include hr hs

/-- Actual invariant lifts exist and have exact, not merely reduced, boundary compatibility. -/
theorem exists_joint_invariant_lifts (hUa : IsAffineOpen U) (hVa : IsAffineOpen V)
    (E : B.Opens) (hE : r ⁻¹ᵁ E = s ⁻¹ᵁ E)
    (hUE : (j₁) ⁻¹ᵁ U ≤ (b₁) ⁻¹ᵁ E) (hVE : (j₂) ⁻¹ᵁ V ≤ (b₂) ⁻¹ᵁ E)
    (t : Γ(E.toScheme, ⊤)) (ht : (r ∣_ E).appTop t = (s.resLE E _ hE.le).appTop t) :
    ∃ (a : invariantCoordinates (restrictedAction τ₁ U hU))
      (b : invariantCoordinates (restrictedAction τ₂ V hV)),
      ((j₁) ∣_ U).appTop a.val = ((b₁).resLE E _ hUE).appTop t ∧
      ((j₂) ∣_ V).appTop b.val = ((b₂).resLE E _ hVE).appTop t ∧
      (jointChartFirst e o o' α β U V).appTop a.val -
        (jointChartSecond e o o' α β U V).appTop b.val ∈
          RingHom.ker ((j) ∣_ W).appTop.hom := by
  obtain ⟨a, ha⟩ := domainInvariantCoefficient_lift e I o i z r s hr hs
    E hE U hU hUE t ht hUa
  obtain ⟨b, hb⟩ := domainInvariantCoefficient_lift e J o' i z r s hr hs
    E hE V hV hVE t ht hVa
  have ha' : ((j₁) ∣_ U).appTop a.val = ((b₁).resLE E _ hUE).appTop t :=
    congrArg Subtype.val ha
  have hb' : ((j₂) ∣_ V).appTop b.val = ((b₂).resLE E _ hVE).appTop t :=
    congrArg Subtype.val hb
  exact ⟨a, b, ha', hb', jointChart_lifts_sub_mem_kernel e o o' α β U V
    i z r s hr hs E hE hUE hVE t ht a.val b.val ha' hb'⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
