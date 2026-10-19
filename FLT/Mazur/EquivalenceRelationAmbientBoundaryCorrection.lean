/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteBoundaryCorrections

/-!
# One ambient boundary correction for every complete test

Lift the original invariant boundary value on the ambient affine source once.
Subtracting that lift constructs an ambient boundary-zero coefficient. Its
discrepancy agrees with the prescribed discrepancy on every complete test,
including nonreduced tests. No completeness of the ambient source is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open SchemeFiniteGroupQuotient SourceRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  {S B : Scheme} (j : S ⟶ source p q I o) [Mono j] [IsAffine S]
  (ρ : Equiv.Perm I →* Aut S)
  (hj : ∀ g, (ρ g).hom ≫ j = j ≫ (action e I o g).hom)
  (i : B ⟶ source p q I o) [IsClosedImmersion i]
  (τ : Equiv.Perm I →* Aut B)
  (hi : ∀ g, (τ g).hom ≫ i = i ≫ (action e I o g).hom)
local notation "β" => FiniteGroupEquivariantPullback.action ρ τ (action e I o) j i hj hi
local notation "b" => pullback.fst j i

omit [Etale p] [Mono j] in
/-- Choose one ambient invariant lift, before choosing any order or complete test. -/
theorem exists_ambient_boundary_correction
    (t : invariantCoordinates β) (a : Γ(S, ⊤)) (ha : (b).appTop a = t.val) :
    ∃ z : Γ(S, ⊤), (b).appTop z = 0 ∧
      ∃ v : invariantCoordinates ρ, a - z = v.val := by
  obtain ⟨v, hv⟩ := completeBoundary_invariant_surjective e I o j ρ hj i τ hi t
  have hv' : (b).appTop v.val = t.val := congrArg Subtype.val hv
  refine ⟨a - v.val, ?_, v, ?_⟩
  · rw [map_sub, ha, hv', sub_self]
  · ring

omit [IsAffine S] in
include e hj in
/-- An ambient invariant difference gives exact agreement on every complete first support. -/
theorem ambient_correction_complete_test
    (a z : Γ(S, ⊤)) (v : invariantCoordinates ρ) (hv : a - z = v.val)
    {T : Scheme} (w : T ⟶ fullRelation p q I o) (u u' : T ⟶ S)
    (hu : u ≫ j = w ≫ relationFirst p q I o)
    (hu' : u' ≫ j = w ≫ relationSecond p q I o)
    (hc : Set.range (w ≫ relationFirst p q I o) ⊆
      completePointLocus (p := p) (q := q) I o) :
    u.appTop z - u'.appTop z = u.appTop a - u'.appTop a := by
  have he := completeEquivariant_invariant_test_of_support e I o j ρ hj v w u u' hu hu' hc
  rw [← hv, map_sub, map_sub] at he
  linear_combination -he

/-- One actual ambient correction works simultaneously for all complete relation tests. -/
theorem exists_ambient_boundary_correction_all_tests
    (t : invariantCoordinates β) (a : Γ(S, ⊤)) (ha : (b).appTop a = t.val) :
    ∃ z : Γ(S, ⊤), (b).appTop z = 0 ∧
      ∀ (T : Scheme) (w : T ⟶ fullRelation p q I o) (u u' : T ⟶ S),
        u ≫ j = w ≫ relationFirst p q I o →
        u' ≫ j = w ≫ relationSecond p q I o →
        Set.range (w ≫ relationFirst p q I o) ⊆
          completePointLocus (p := p) (q := q) I o →
        u.appTop z - u'.appTop z = u.appTop a - u'.appTop a := by
  obtain ⟨z, hz, v, hv⟩ := exists_ambient_boundary_correction e I o j ρ hj i τ hi t a ha
  exact ⟨z, hz, fun _ w u u' hu hu' hc ↦
    ambient_correction_complete_test e I o j ρ hj a z v hv w u u' hu hu' hc⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
