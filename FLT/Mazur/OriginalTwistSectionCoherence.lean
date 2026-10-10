/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalFamilyIdentityComparison
public import FLT.Mazur.OriginalFamilySectionComposition
public import FLT.Mazur.SheafPullbackPathPentagon

/-!
# Representative-level coherence of original twist transport

Both unit triangles, associativity, and the four-pullback pentagon hold on
the actual tensor sections. No quotient or divisor reconstruction is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.CartierAbel
open FCurve SheafPullbackPathComparison
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor
variable {P A B C D E : Scheme.{u}} (q : P ⟶ A) (L : P.Modules)

/-- Apply an actual base morphism to a tensor section on the original total space. -/
def originalTwistSectionMap {M N : A.Modules} (a : M ⟶ N)
    (t : Γ(ModuleSheafTensor.tensor L ((pullback q).obj M), ⊤)) :
    Γ(ModuleSheafTensor.tensor L ((pullback q).obj N), ⊤) :=
  (ModuleSheafTensor.map (𝟙 L) ((pullback q).map a)).app ⊤ t

/-- Composing actual base morphisms composes their actions on original sections. -/
lemma originalTwistSectionMap_comp {M N O : A.Modules} (a : M ⟶ N) (b : N ⟶ O)
    (t : Γ(ModuleSheafTensor.tensor L ((pullback q).obj M), ⊤)) :
    originalTwistSectionMap q L (a ≫ b) t =
      originalTwistSectionMap q L b (originalTwistSectionMap q L a t) := by
  unfold originalTwistSectionMap
  rw [CategoryTheory.Functor.map_comp]
  have hm := ModuleSheafTensor.map_comp (𝟙 L) (𝟙 L)
    ((pullback q).map a) ((pullback q).map b)
  simp only [Category.comp_id] at hm
  rw [hm]
  rfl

/-- The right unit triangle agrees on the actual original tensor section. -/
lemma originalTwistSectionMap_right_unit (f : A ⟶ B) (M : B.Modules)
    (t : Γ(ModuleSheafTensor.tensor L
      ((pullback q).obj ((pullback f).obj ((pullback (𝟙 B)).obj M))), ⊤)) :
    originalTwistSectionMap q L
      ((comparison f (𝟙 B) f (Category.comp_id f)).hom.app M) t =
    originalTwistSectionMap q L ((pullback f).map ((pullbackId B).hom.app M)) t := by
  rw [comparison_comp_id]

/-- The left unit triangle agrees on the actual original tensor section. -/
lemma originalTwistSectionMap_left_unit (f : A ⟶ B) (M : B.Modules)
    (t : Γ(ModuleSheafTensor.tensor L
      ((pullback q).obj ((pullback (𝟙 A)).obj ((pullback f).obj M))), ⊤)) :
    originalTwistSectionMap q L
      ((comparison (𝟙 A) f f (Category.id_comp f)).hom.app M) t =
    originalTwistSectionMap q L ((pullbackId A).hom.app ((pullback f).obj M)) t := by
  rw [comparison_id_comp]

/-- Both prescribed three-pullback paths agree before taking any original section orbit. -/
lemma originalTwistSectionMap_assoc (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (M : D.Modules) (t : Γ(ModuleSheafTensor.tensor L
      ((pullback q).obj ((pullback f).obj ((pullback g).obj ((pullback h).obj M)))), ⊤)) :
    originalTwistSectionMap q L
      ((pullback f).map ((pullbackComp g h).hom.app M) ≫
        (pullbackComp f (g ≫ h)).hom.app M ≫
        (pullbackCongr (Category.assoc f g h).symm).hom.app M) t =
    originalTwistSectionMap q L
      ((pullbackComp f g).hom.app ((pullback h).obj M) ≫
        (pullbackComp (f ≫ g) h).hom.app M) t := by
  rw [comp_assoc]

/-- The pentagon holds on arbitrary actual sections of the iterated original twist. -/
lemma originalTwistSectionMap_pentagon (f : A ⟶ B) (g : B ⟶ C)
    (h : C ⟶ D) (i : D ⟶ E) (M : E.Modules)
    (t : Γ(ModuleSheafTensor.tensor L ((pullback q).obj
      ((pullback f).obj ((pullback g).obj ((pullback h).obj ((pullback i).obj M))))), ⊤)) :
    originalTwistSectionMap q L
      ((pullback f).map ((pullback g).map ((pullbackComp h i).hom.app M)) ≫
        (pullback f).map ((pullbackComp g (h ≫ i)).hom.app M) ≫
        (comparison f (g ≫ (h ≫ i)) (((f ≫ g) ≫ h) ≫ i)
          (by simp only [Category.assoc])).hom.app M) t =
    originalTwistSectionMap q L
      ((pullbackComp f g).hom.app ((pullback h).obj ((pullback i).obj M)) ≫
        (pullbackComp (f ≫ g) h).hom.app ((pullback i).obj M) ≫
        (pullbackComp ((f ≫ g) ≫ h) i).hom.app M) t := by
  rw [comparison_pentagon]

end FLT.Mazur.CartierAbel
