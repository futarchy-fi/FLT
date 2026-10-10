/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackPathComparison

/-!
# Pentagon for prescribed sheaf pullback paths

The two extreme parenthesizations of four actual pullbacks normalize to the
same map. Intermediate vertices are the prescribed composition comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SheafPullbackPathComparison
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {A B C D E : Scheme.{u}}

/-- Four successive pullbacks satisfy the pentagon with their prescribed comparisons. -/
@[reassoc]
lemma comparison_pentagon (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (i : D ⟶ E)
    (M : E.Modules) :
    (pullback f).map ((pullback g).map ((pullbackComp h i).hom.app M)) ≫
      (pullback f).map ((pullbackComp g (h ≫ i)).hom.app M) ≫
      (comparison f (g ≫ (h ≫ i)) (((f ≫ g) ≫ h) ≫ i)
        (by simp only [Category.assoc])).hom.app M =
    (pullbackComp f g).hom.app ((pullback h).obj ((pullback i).obj M)) ≫
      (pullbackComp (f ≫ g) h).hom.app ((pullback i).obj M) ≫
      (pullbackComp ((f ≫ g) ≫ h) i).hom.app M := by
  have h₁ := comparison_assoc f g (h ≫ i) (f ≫ g) (g ≫ (h ≫ i))
    (((f ≫ g) ≫ h) ≫ i) rfl rfl (by simp only [Category.assoc])
      (Category.assoc (f ≫ g) h i).symm M
  have h₂ := comparison_assoc (f ≫ g) h i ((f ≫ g) ≫ h) (h ≫ i)
    (((f ≫ g) ≫ h) ≫ i) rfl rfl (Category.assoc (f ≫ g) h i).symm rfl M
  have hn := (pullbackComp f g).hom.naturality ((pullbackComp h i).hom.app M)
  simp only [comparison, pullbackCongr, eqToIso_refl, Iso.trans_refl] at h₁ h₂ ⊢
  rw [h₁]
  change (pullback g ⋙ pullback f).map ((pullbackComp h i).hom.app M) ≫ _ = _
  rw [← Category.assoc, hn]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun z ↦ (pullbackComp f g).hom.app
      ((pullback h).obj ((pullback i).obj M)) ≫ z) h₂)

end FLT.Mazur.SheafPullbackPathComparison
