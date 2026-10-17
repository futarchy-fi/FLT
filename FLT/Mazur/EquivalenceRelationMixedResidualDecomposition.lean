/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationMixedResidualPieces
public import FLT.Mazur.SchemeCoproductSections

/-!
# Splitting every original mixed test as actual schemes and coefficient rings

The disjoint coproduct is isomorphic to the entire test, retaining the residual
piece and every independent embedding graph. Coefficient projections are the
actual restriction maps, so all nilpotent equations remain visible.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  [(source p q J o').IsSeparated]
  {T : Scheme.{0}} (z : T ⟶ relation p q I J o o')

/-- The actual coproduct map retains every original open inclusion. -/
def mixedResidualBranchMap :
    (∐ fun a ↦ (mixedResidualBranchOpen e o o' z a).toScheme) ⟶ T :=
  Sigma.desc fun a ↦ (mixedResidualBranchOpen e o o' z a).ι

instance mixedResidualBranchMap_open : IsOpenImmersion (mixedResidualBranchMap e o o' z) := by
  apply isOpenImmersion_sigmaDesc
  intro a b h
  simpa only [Scheme.Opens.range_ι] using mixedResidualBranchOpen_disjoint e o o' z a b h

/-- This coproduct covers the full original relation, with no support reduction. -/
def mixedResidualBranchIso :
    (∐ fun a ↦ (mixedResidualBranchOpen e o o' z a).toScheme) ≅ T := by
  have hs : Function.Surjective (mixedResidualBranchMap e o o' z) := by
    intro x
    have hx := mixedResidualBranchOpen_covers e o o' z x
    obtain ⟨a, ha⟩ := hx
    refine ⟨Sigma.ι (fun b ↦ (mixedResidualBranchOpen e o o' z b).toScheme) a ⟨x, ha⟩, ?_⟩
    change (Sigma.ι _ a ≫ mixedResidualBranchMap e o o' z) ⟨x, ha⟩ = x
    rw [mixedResidualBranchMap, Sigma.ι_comp_desc]
    rfl
  let _ := (isIso_iff_isOpenImmersion_and_surjective
    (mixedResidualBranchMap e o o' z)).mpr ⟨inferInstance, ⟨hs⟩⟩
  exact asIso (mixedResidualBranchMap e o o' z)

/-- The decomposition keeps each original branch inclusion as an exact scheme morphism. -/
@[reassoc] theorem mixedResidualBranchIso_component (a : Option (J ↪ I)) :
    Sigma.ι _ a ≫ (mixedResidualBranchIso e o o' z).hom =
      (mixedResidualBranchOpen e o o' z a).ι := Sigma.ι_comp_desc _ _

/-- The full coefficient ring is the product of the residual and original embedding rings. -/
def mixedResidualBranchSectionsIso : Γ(T, ⊤) ≅
    CommRingCat.of (∀ a, Γ((mixedResidualBranchOpen e o o' z a).toScheme, ⊤)) :=
  Scheme.Γ.mapIso (mixedResidualBranchIso e o o' z).op ≪≫ SchemeCoproductSections.iso _

/-- Every coefficient projection is the actual restriction to the corresponding branch. -/
theorem mixedResidualBranchSectionsIso_apply (t : Γ(T, ⊤))
    (a : Option (J ↪ I)) :
    (mixedResidualBranchSectionsIso e o o' z).hom t a =
      (mixedResidualBranchOpen e o o' z a).ι.appTop t := by
  change (SchemeCoproductSections.iso _).hom
    ((mixedResidualBranchIso e o o' z).hom.appTop t) a = _
  rw [SchemeCoproductSections.iso_apply]
  change (((mixedResidualBranchIso e o o' z).hom.appTop ≫
    (Sigma.ι (fun b ↦ (mixedResidualBranchOpen e o o' z b).toScheme) a).appTop) t) = _
  rw [← Scheme.Hom.comp_appTop, mixedResidualBranchIso_component]

/-- All branch restrictions jointly detect exact equality, including nilpotents. -/
theorem mixedResidualBranch_sections_eq_iff (a b : Γ(T, ⊤)) :
    a = b ↔ ∀ c : Option (J ↪ I),
      (mixedResidualBranchOpen e o o' z c).ι.appTop a =
        (mixedResidualBranchOpen e o o' z c).ι.appTop b := by
  constructor
  · rintro rfl c
    rfl
  · intro h
    apply (ConcreteCategory.bijective_of_isIso
      (mixedResidualBranchSectionsIso e o o' z).hom).injective
    funext c
    exact (mixedResidualBranchSectionsIso_apply e o o' z a c).trans
      ((h c).trans (mixedResidualBranchSectionsIso_apply e o o' z b c).symm)

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
