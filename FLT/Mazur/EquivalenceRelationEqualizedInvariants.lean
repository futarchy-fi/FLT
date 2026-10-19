/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationRestrictedActionGraphs

/-!
# Recovering moving invariants from the full original relation equation

Pulling an exact equation back along each actual action graph constructs the
invariant coefficient. On complete support this is an equivalence, including
nonreduced coefficients. In particular, a stage correction equation supplies
its own invariant difference rather than requiring an extra witness.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open SchemeFiniteGroupQuotient SourceRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  {S : Scheme} (j : S ⟶ source p q I o) [Mono j]
  (ρ : Equiv.Perm I →* Aut S)
  (hj : ∀ g, (ρ g).hom ≫ j = j ≫ (action e I o g).hom)
local notation "r" => SourceRestriction.fst j j
local notation "s" => SourceRestriction.snd j j

include e hj in
omit [Etale p] [Mono j] in
/-- Exact original equalization constructs a moving-invariant coefficient. -/
theorem exists_invariant_of_original_equalizes (a : Γ(S, ⊤))
    (ha : (r).appTop a = (s).appTop a) :
    ∃ v : invariantCoordinates ρ, v.val = a := by
  refine ⟨⟨a, ?_⟩, rfl⟩
  intro g
  have h := congrArg
    (fun t ↦ (restrictedActionGraph e I o j ρ hj g⁻¹).appTop t) ha
  change ((r).appTop ≫ (restrictedActionGraph e I o j ρ hj g⁻¹).appTop) a =
    ((s).appTop ≫ (restrictedActionGraph e I o j ρ hj g⁻¹).appTop) a at h
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
    restrictedActionGraph_first, restrictedActionGraph_second] at h
  exact h.symm

include e hj in
/-- On complete support the full original equalizer is precisely the moving fixed ring. -/
theorem original_equalizes_iff_invariant
    (hc : Set.range j ⊆ completePointLocus (p := p) (q := q) I o) (a : Γ(S, ⊤)) :
    (r).appTop a = (s).appTop a ↔ ∃ v : invariantCoordinates ρ, v.val = a := by
  constructor
  · exact exists_invariant_of_original_equalizes e I o j ρ hj a
  · rintro ⟨v, rfl⟩
    exact completeEquivariant_invariant_equalizes e I o j ρ hj hc v

include e hj in
omit [Etale p] [Mono j] in
/-- A correction of the full discrepancy constructs the invariant difference itself. -/
theorem exists_invariant_of_original_correction (a z : Γ(S, ⊤))
    (h : (r).appTop z - (s).appTop z = (r).appTop a - (s).appTop a) :
    ∃ v : invariantCoordinates ρ, a - z = v.val := by
  obtain ⟨v, hv⟩ := exists_invariant_of_original_equalizes e I o j ρ hj (a - z) (by
    rw [map_sub, map_sub]
    linear_combination -h)
  exact ⟨v, hv.symm⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
