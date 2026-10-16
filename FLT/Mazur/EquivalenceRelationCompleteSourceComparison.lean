/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompletePointLocus

/-!
# Scheme tests supported on complete original frames

An arbitrary scheme test of the full original relation factors uniquely through
the permutation comparison if its first endpoint has complete support. The test
need not be reduced, affine, or a field spectrum. The permutation may vary between
open and closed pieces of the test. This does not construct an etale neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  {T : Scheme.{0}} (z : T ⟶ fullRelation p q I o)

/-- Complete first-endpoint support puts every original arrow in the comparison image. -/
theorem complete_source_range
    (hz : Set.range (z ≫ relationFirst p q I o) ⊆
      completePointLocus (p := p) (q := q) I o) :
    Set.range z ⊆ Set.range (relationComparison e I o) := by
  rintro _ ⟨x, rfl⟩
  let v := T.fromSpecResidueField x ≫ z
  have hx : v default = z x := by
    change z (T.fromSpecResidueField x default) = z x
    rw [Scheme.fromSpecResidueField_apply]
  have hc : Complete I o (v ≫ relationFirst p q I o) := by
    rw [complete_iff_mem_completePointLocus]
    change relationFirst p q I o (v default) ∈ _
    rw [hx]
    exact hz ⟨x, rfl⟩
  obtain ⟨w, hw⟩ := complete_first_factors_relationComparison e I o v hc
  exact ⟨w default, (congrArg (fun f ↦ f default) hw).trans hx⟩

/-- The unique scheme-level permutation lift retains nonreduced test schemes. -/
def completeSourceLift
    (hz : Set.range (z ≫ relationFirst p q I o) ⊆
      completePointLocus (p := p) (q := q) I o) :
    T ⟶ permutationRelation (p := p) (q := q) I o := by
  let _ := relationComparison_isOpenImmersion e I o
  exact IsOpenImmersion.lift _ z (complete_source_range e I o z hz)

/-- The lift retains the entire original relation morphism. -/
@[reassoc] theorem completeSourceLift_comparison
    (hz : Set.range (z ≫ relationFirst p q I o) ⊆
      completePointLocus (p := p) (q := q) I o) :
    completeSourceLift e I o z hz ≫ relationComparison e I o = z := by
  let _ := relationComparison_isOpenImmersion e I o
  exact IsOpenImmersion.lift_fac _ z (complete_source_range e I o z hz)

/-- No choice of local permutations changes the resulting global lift. -/
theorem completeSourceLift_unique
    (hz : Set.range (z ≫ relationFirst p q I o) ⊆
      completePointLocus (p := p) (q := q) I o)
    (w : T ⟶ permutationRelation (p := p) (q := q) I o)
    (hw : w ≫ relationComparison e I o = z) : w = completeSourceLift e I o z hz := by
  let _ := relationComparison_isOpenImmersion e I o
  apply (cancel_mono (relationComparison e I o)).mp
  exact hw.trans (completeSourceLift_comparison e I o z hz).symm

omit [Etale p] in
/-- Complete support is stable under every change of the test scheme. -/
theorem complete_source_precomp {T' : Scheme.{0}} (a : T' ⟶ T)
    (hz : Set.range (z ≫ relationFirst p q I o) ⊆
      completePointLocus (p := p) (q := q) I o) :
    Set.range ((a ≫ z) ≫ relationFirst p q I o) ⊆
      completePointLocus (p := p) (q := q) I o := by
  rintro _ ⟨x, rfl⟩
  exact hz ⟨a x, rfl⟩

/-- Permutation lifts commute with arbitrary test changes, including thickenings. -/
@[reassoc] theorem completeSourceLift_naturality {T' : Scheme.{0}} (a : T' ⟶ T)
    (hz : Set.range (z ≫ relationFirst p q I o) ⊆
      completePointLocus (p := p) (q := q) I o) :
    a ≫ completeSourceLift e I o z hz =
      completeSourceLift e I o (a ≫ z) (complete_source_precomp I o z a hz) := by
  apply completeSourceLift_unique
  rw [Category.assoc, completeSourceLift_comparison]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
