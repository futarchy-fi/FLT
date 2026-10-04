/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveFiniteSubgroup
public import FLT.Mazur.RelativeSums

/-!
# Base change of group sections and their powers

The monoidal pullback of a group section is the canonical scheme section
on the fiber product. It preserves powers and the associated section ideals.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GroupSectionBaseChange
variable {S T : Scheme} (g : T ⟶ S) {G X : Over S}

/-- Base change of a section, using the canonical monoidal unit comparison. -/
def pullSection (s : 𝟙_ (Over S) ⟶ X) : 𝟙_ (Over T) ⟶ (Over.pullback g).obj X :=
  Functor.LaxMonoidal.ε (Over.pullback g) ≫ (Over.pullback g).map s

/-- The pulled-back section retains its original section after projection. -/
@[reassoc (attr := simp)]
theorem section_fst (s : 𝟙_ (Over S) ⟶ X) :
    (pullSection g s).left ≫ pullback.fst X.hom g = g ≫ s.left := by
  simp only [pullSection, Over.comp_left, Over.pullback_map_left, Category.assoc,
    pullback.lift_fst, Over.ε_pullback_left]
  have he : pullback.fst (𝟙 S) g = pullback.snd (𝟙 S) g ≫ g := by
    simpa using pullback.condition (f := 𝟙 S) (g := g)
  change inv (pullback.snd (𝟙 S) g) ≫ pullback.fst (𝟙 S) g ≫ s.left = _
  rw [he, Category.assoc, IsIso.inv_hom_id_assoc]

/-- The section agrees with the scheme-theoretic section used for divisor pullback. -/
theorem section_left (s : 𝟙_ (Over S) ⟶ X) :
    (pullSection g s).left = FCurve.sectionBaseChange X.hom g s.left s.w := by
  apply pullback.hom_ext
  · simp [FCurve.sectionBaseChange]
  · exact (pullSection g s).w.trans (FCurve.sectionBaseChange_snd _ _ _ _).symm

/-- Base change commutes with postcomposition of sections. -/
theorem section_comp (s : 𝟙_ (Over S) ⟶ G) (f : G ⟶ X) :
    pullSection g (s ≫ f) = pullSection g s ≫ (Over.pullback g).map f := by
  simp [pullSection]

/-- The powers of a group section pull back to powers of its pullback. -/
theorem section_pow [MonObj G] (s : 𝟙_ (Over S) ⟶ G) (i : ℕ) :
    pullSection g (s ^ i) = pullSection g s ^ i := by
  change Functor.LaxMonoidal.ε (Over.pullback g) ≫
    (Over.pullback g).homMonoidHom (s ^ i) = _
  rw [map_pow, MonObj.comp_pow]
  rfl

/-- The section divisor has its actual scheme-theoretic pullback ideal. -/
theorem section_ker [IsSeparated X.hom] (s : 𝟙_ (Over S) ⟶ X) :
    (pullSection g s).left.ker = s.left.ker.comap (pullback.fst X.hom g) := by
  rw [section_left]
  exact FCurve.ker_sectionBaseChange _ _ _ _

end FLT.Mazur.GroupSectionBaseChange
