/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteTestPartition
public import FLT.Mazur.SchemeCoproductSections

/-!
# Finite coefficient products for complete-support original relation tests

Global functions on an arbitrary complete-support test are exactly the product
of functions on its permutation pieces. The projections are the actual restriction
maps, and original relation coefficients retain the moving first endpoint.
No completeness assertion for arbitrary original boundary sections is made here.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  {T : Scheme.{0}} (z : T ⟶ fullRelation p q I o)
  (hz : Set.range (z ≫ relationFirst p q I o) ⊆
    completePointLocus (p := p) (q := q) I o)

/-- The actual coefficient ring is the finite product of its permutation-piece rings. -/
def permutationTestSectionsIso : Γ(T, ⊤) ≅
    CommRingCat.of (∀ σ : Equiv.Perm I, Γ((permutationTestOpen e I o z σ).toScheme, ⊤)) :=
  Scheme.Γ.mapIso (permutationTestIso e I o z hz).op ≪≫
    SchemeCoproductSections.iso _

/-- Product projection is precisely the original open restriction of coefficients. -/
theorem permutationTestSectionsIso_apply (r : Γ(T, ⊤)) (σ : Equiv.Perm I) :
    (permutationTestSectionsIso e I o z hz).hom r σ =
      (permutationTestOpen e I o z σ).ι.appTop r := by
  change (SchemeCoproductSections.iso _).hom
    ((permutationTestIso e I o z hz).hom.appTop r) σ = _
  rw [SchemeCoproductSections.iso_apply]
  change (((permutationTestIso e I o z hz).hom.appTop ≫
    (Sigma.ι (fun τ ↦ (permutationTestOpen e I o z τ).toScheme) σ).appTop) r) = _
  rw [← Scheme.Hom.comp_appTop, permutationTestIso_component]

include hz in
/-- Actual coefficient equality is detected on all finite permutation pieces. -/
theorem permutationTest_sections_ext {r s : Γ(T, ⊤)}
    (h : ∀ σ : Equiv.Perm I,
      (permutationTestOpen e I o z σ).ι.appTop r =
        (permutationTestOpen e I o z σ).ι.appTop s) : r = s := by
  apply (permutationTestSectionsIso e I o z hz).commRingCatIsoToRingEquiv.injective
  change (permutationTestSectionsIso e I o z hz).hom r =
    (permutationTestSectionsIso e I o z hz).hom s
  funext σ
  exact (permutationTestSectionsIso_apply e I o z hz r σ).trans
    ((h σ).trans (permutationTestSectionsIso_apply e I o z hz s σ).symm)

/-- Original relation coefficients use the exact moving-endpoint arrow on each piece. -/
theorem permutationTestSectionsIso_original (r : Γ(D, ⊤)) (σ : Equiv.Perm I) :
    (permutationTestSectionsIso e I o z hz).hom ((z ≫ relationArrow p q I o).appTop r) σ =
      ((permutationTestOpen e I o z σ).ι ≫ z ≫ relationFirst p q I o ≫
        actionArrow I o σ).appTop r := by
  rw [permutationTestSectionsIso_apply]
  change (((z ≫ relationArrow p q I o).appTop ≫
    (permutationTestOpen e I o z σ).ι.appTop) r) = _
  rw [← Scheme.Hom.comp_appTop, permutationTestOpen_arrow]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
