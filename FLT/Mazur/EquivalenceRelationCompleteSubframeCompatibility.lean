/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationMixedResidualDecomposition
public import FLT.Mazur.EquivalenceRelationSubframeFullDomain

/-!
# Full mixed compatibility on complete source charts

A test supported on complete first frames has an empty residual open. Its
embedding equations therefore detect equality on the whole original scheme.
Consequently a selected lift from an invariant complete source chart solves
the full mixed equation, with no missing residual coefficient.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  [(source p q J o').IsSeparated]
  {T : Scheme.{0}} (z : T ⟶ relation p q I J o o')
  (hz : Set.range (z ≫ fst p q I J o o') ⊆ completePointLocus (p := p) (q := q) I o)

include hz in
/-- The full residual scheme is empty when the entire first support is complete. -/
theorem completeMixedResidual_isEmpty : IsEmpty (mixedResidualTestOpen e o o' z).toScheme :=
  ⟨fun x ↦ mixedResidualTestOpen_first_incomplete e o o' z x (hz ⟨x.val, rfl⟩)⟩

include hz in
/-- All embedding tests detect exact coefficients on a complete-supported mixed test. -/
theorem completeMixed_embedding_sections_ext {u v : Γ(T, ⊤)}
    (h : ∀ ι : J ↪ I, (mixedEmbeddingTestOpen e o o' z ι).ι.appTop u =
      (mixedEmbeddingTestOpen e o o' z ι).ι.appTop v) : u = v := by
  apply (mixedResidualBranch_sections_eq_iff e o o' z u v).mpr
  intro a
  cases a with
  | none =>
    let _ := completeMixedResidual_isEmpty e o o' z hz
    change (mixedResidualTestOpen e o o' z).ι.appTop u =
      (mixedResidualTestOpen e o o' z).ι.appTop v
    exact Subsingleton.elim _ _
  | some ι => exact h ι

variable (U : (source p q I o).Opens) (V : (source p q J o').Opens)
  (hU : ∀ σ, (action e I o σ).hom ⁻¹ᵁ U = U)
  (h : ∀ ι : J ↪ I, U ≤ subframeMap e o o' ι ⁻¹ᵁ V)
  (hc : (U : Set _) ⊆ completePointLocus (p := p) (q := q) I o)

include hc in
/-- Selected pullback from a complete invariant source solves the entire mixed equation. -/
theorem completeSubframeLift_mixed
    (ι : J ↪ I) (u : invariantCoordinates (restrictedAction (action e I o) U hU))
    (v : Γ(V.toScheme, ⊤))
    (hv : (subframeRefinementMap e o o' ι U V (h ι)).appTop v = u.val) :
    (mixedChartFirst o o' U V).appTop u.val =
      (mixedChartSecond o o' U V).appTop v := by
  have hs : Set.range ((mixedChartOpen o o' U V).ι ≫ fst p q I J o o') ⊆
      completePointLocus (p := p) (q := q) I o := by
    rintro _ ⟨x, rfl⟩
    exact hc x.property.1
  apply completeMixed_embedding_sections_ext e o o' (mixedChartOpen o o' U V).ι hs
  intro κ
  change ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι κ).ι ≫
    mixedChartFirst o o' U V).appTop u.val =
    ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι κ).ι ≫
      mixedChartSecond o o' U V).appTop v
  apply (mixedSubframeBranch_equation_iff e o o' U V κ (h κ) u.val v).mpr
  have he := (subframePullback_invariant_iff e o o' U hU V h ι v).mp ⟨u, hv.symm⟩
  exact hv.symm.trans (he κ).symm

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
