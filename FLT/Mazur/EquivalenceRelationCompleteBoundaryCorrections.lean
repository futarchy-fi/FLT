/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteEquivariantCoefficients
public import FLT.Mazur.FiniteGroupEquivariantPullback

/-!
# Actual boundary-kernel corrections on complete affine sources

Pull back the original equivariant closed boundary to a complete affine source.
Freeness constructs invariant lifts. Subtracting such a lift gives an element
of the exact boundary kernel whose discrepancy is the full original discrepancy.
No extension to an ambient incomplete source is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open SchemeFiniteGroupQuotient SourceRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  {S B : Scheme.{0}} (j : S ⟶ source p q I o) [Mono j]
  (ρ : Equiv.Perm I →* Aut S)
  (hj : ∀ σ, (ρ σ).hom ≫ j = j ≫ (action e I o σ).hom)
  (i : B ⟶ source p q I o) [IsClosedImmersion i]
  (τ : Equiv.Perm I →* Aut B)
  (hi : ∀ σ, (τ σ).hom ≫ i = i ≫ (action e I o σ).hom)
local notation "β" => FiniteGroupEquivariantPullback.action ρ τ (action e I o) j i hj hi
local notation "b" => pullback.fst j i
local notation "hb" => FiniteGroupEquivariantPullback.action_fst ρ τ (action e I o) j i hj hi

omit [Mono j] [Etale p] in
include hj in
/-- The induced action on any monomorphic source is free on every nonempty test. -/
theorem completeSource_action_free {T : Scheme} [Nonempty T] (a : T ⟶ S)
    (σ : Equiv.Perm I) (ha : a ≫ (ρ σ).hom = a) : σ = 1 := by
  apply action_free e I o (a ≫ j) σ
  have h := congrArg (fun f ↦ f ≫ j) ha
  simpa only [Category.assoc, hj] using h

variable [IsAffine S]

omit [Mono j] [Etale p] in
/-- Every invariant boundary function has an invariant lift on the full complete source. -/
theorem completeBoundary_invariant_surjective :
    Function.Surjective (invariantMap β ρ b hb) :=
  invariantMap_surjective_of_free ρ
    (fun _ _ a σ ha ↦ completeSource_action_free e I o j ρ hj a σ ha) β b hb

/-- A supplied boundary lift admits a correction in the exact original boundary kernel. -/
theorem completeBoundary_exists_kernel_correction
    (hc : Set.range j ⊆ completePointLocus (p := p) (q := q) I o)
    (t : invariantCoordinates β) (u : Γ(S, ⊤)) (hu : (b).appTop u = t.val) :
    ∃ z : Γ(S, ⊤), (b).appTop z = 0 ∧
      (SourceRestriction.fst j j).appTop z - (SourceRestriction.snd j j).appTop z =
        (SourceRestriction.fst j j).appTop u - (SourceRestriction.snd j j).appTop u := by
  obtain ⟨w, hw⟩ := completeBoundary_invariant_surjective e I o j ρ hj i τ hi t
  have hw' : (b).appTop w.val = t.val := congrArg Subtype.val hw
  have he := completeEquivariant_invariant_equalizes e I o j ρ hj hc w
  refine ⟨u - w.val, ?_, ?_⟩
  · rw [map_sub, hu, hw', sub_self]
  · rw [map_sub, map_sub, he]
    ring

omit [Mono j] [Etale p] [IsClosedImmersion i] in
/-- The exact boundary ideal is recovered from its invariant equations, including nilpotents. -/
theorem completeBoundary_kernel_extension :
    (RingHom.ker (invariantMap β ρ b hb)).map
      (let _ := SchemeCoordinateAction.coordinateAction ρ
       FiniteGroupQuotient.inclusion (Equiv.Perm I) Γ(S, ⊤)) =
        RingHom.ker (b).appTop.hom :=
  invariantMap_ker_extension β ρ b hb
    (fun _ _ a σ ha ↦ completeSource_action_free e I o j ρ hj a σ ha)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
