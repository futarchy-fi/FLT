/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedFrameRelation
public import FLT.Mazur.EquivalenceRelationNormalizedFrameComparison

/-!
# Open action graphs inside the full original normalized relation

Each normalized permutation gives an actual open section of the first projection
of the full original relation. Factorization through this graph is equivalent to
the exact action equation on arbitrary scheme tests, including nonreduced tests.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)

/-- The action graph retains the actual original transition arrow. -/
def actionGraph (σ : Equiv.Perm I) : source p q I o ⟶ fullRelation p q I o :=
  relationLift p q I o (𝟙 _) (action e I o σ).hom (actionArrow I o σ)
    (by rw [Category.id_comp]; exact actionArrow_first I o σ)
    (actionArrow_second e I o σ)

/-- Each action graph is a section of the first full relation projection. -/
@[reassoc] theorem actionGraph_first (σ : Equiv.Perm I) :
    actionGraph e I o σ ≫ relationFirst p q I o = 𝟙 _ :=
  relationLift_first p q I o _ _ _ _ _

/-- The independent second endpoint on a graph is its actual normalized action. -/
@[reassoc] theorem actionGraph_second (σ : Equiv.Perm I) :
    actionGraph e I o σ ≫ relationSecond p q I o = (action e I o σ).hom :=
  relationLift_second p q I o _ _ _ _ _

/-- The graph carries the full original relation coordinate, not just a pointwise arrow. -/
@[reassoc] theorem actionGraph_arrow (σ : Equiv.Perm I) :
    actionGraph e I o σ ≫ relationArrow p q I o = actionArrow I o σ :=
  relationLift_arrow p q I o _ _ _ _ _

/-- Each graph embeds as an actual open subscheme of the full original relation. -/
theorem actionGraph_isOpenImmersion [Etale p] (σ : Equiv.Perm I) :
    IsOpenImmersion (actionGraph e I o σ) := by
  let _ := relationFirst_etale p q I o e
  exact UnramifiedSectionImmersion.isOpenImmersion (relationFirst p q I o) _
    (actionGraph_first e I o σ)

variable {T : Scheme} (z : T ⟶ fullRelation p q I o) (σ : Equiv.Perm I)

/-- The exact action equation gives scheme-level factorization through its open graph. -/
theorem actionGraph_factor
    (h : (z ≫ relationFirst p q I o) ≫ (action e I o σ).hom =
      z ≫ relationSecond p q I o) :
    (z ≫ relationFirst p q I o) ≫ actionGraph e I o σ = z := by
  apply relation_hom_ext p q I o e
  · rw [Category.assoc, actionGraph_first, Category.comp_id]
  · rw [Category.assoc, actionGraph_second]
    exact h

/-- Membership in an action graph is exactly the original scheme action equation. -/
theorem factors_actionGraph_iff :
    (∃ u : T ⟶ source p q I o, u ≫ actionGraph e I o σ = z) ↔
      (z ≫ relationFirst p q I o) ≫ (action e I o σ).hom =
        z ≫ relationSecond p q I o := by
  constructor
  · rintro ⟨u, rfl⟩
    simp only [Category.assoc, actionGraph_first_assoc, actionGraph_second]
  · intro h
    exact ⟨z ≫ relationFirst p q I o, actionGraph_factor e I o z σ h⟩

/-- A nonempty test cannot factor through two distinct normalized action graphs. -/
theorem actionGraph_unique [Nonempty T] (τ : Equiv.Perm I)
    (hσ : ∃ u : T ⟶ source p q I o, u ≫ actionGraph e I o σ = z)
    (hτ : ∃ v : T ⟶ source p q I o, v ≫ actionGraph e I o τ = z) : σ = τ :=
  action_unique e I o _ _ σ τ
    ((factors_actionGraph_iff e I o z σ).mp hσ)
    ((factors_actionGraph_iff e I o z τ).mp hτ)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
