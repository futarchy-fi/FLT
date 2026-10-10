/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversallyDistinctSections
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Relative markings as sections of the pulled-back group

A marking on a test object gives actual sections of the group over that object's
base scheme. The construction uses the diagonal and the monoidal pullback, and
preserves the group law. Universal injectivity becomes universal distinctness
of the resulting sections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace FLT.Mazur.RelativeMarkingSections

variable {S : Scheme} (U : Over S)

/-- The diagonal section of the pullback of a test object along its own base map. -/
def diagonal : 𝟙_ (Over U.left) ⟶ (Over.pullback U.hom).obj U :=
  Over.homMk (pullback.lift (𝟙 U.left) (𝟙 U.left) (by simp)) (by simp)

/-- A relative point becomes a section of the actual base-changed scheme. -/
def asSection {E : Over S} (f : U ⟶ E) :
    𝟙_ (Over U.left) ⟶ (Over.pullback U.hom).obj E :=
  diagonal U ≫ (Over.pullback U.hom).map f

/-- Projection recovers the original relative point. -/
@[reassoc (attr := simp)] theorem section_fst {E : Over S} (f : U ⟶ E) :
    (asSection U f).left ≫ pullback.fst E.hom U.hom = f.left := by
  simp [asSection, diagonal]

/-- Taking sections preserves the original marking's multiplication. -/
def sectionHom (E : Over S) [GrpObj E] :
    (U ⟶ E) →* (𝟙_ (Over U.left) ⟶ (Over.pullback U.hom).obj E) where
  toFun := asSection U
  map_one' := by simp [asSection, Functor.map_one, MonObj.comp_one]
  map_mul' f g := by simp [asSection, Functor.map_mul, MonObj.comp_mul]

/-- Universally injective relative points give universally distinct sections. -/
theorem universallyDistinct {E : Over S} {Index : Type} (s : Index → (U ⟶ E))
    (hs : ∀ (V : Over S) (g : V ⟶ U), Nonempty V.left →
      Function.Injective (fun i ↦ g ≫ s i)) :
    UniversallyDistinctSections.UniversallyDistinct (fun i ↦ asSection U (s i)) := by
  intro V g hV i j hij
  let W : Over S := Over.mk (V.hom ≫ U.hom)
  let k : W ⟶ U := Over.homMk V.hom rfl
  apply hs W k hV
  apply Over.OverMorphism.ext
  change V.hom ≫ (s i).left = V.hom ≫ (s j).left
  have h := congrArg (fun f : V ⟶ (Over.pullback U.hom).obj E ↦
    f.left ≫ pullback.fst E.hom U.hom) hij
  have hg : g.left = V.hom := by simpa using g.w
  simpa only [Over.comp_left, Category.assoc, section_fst, hg] using h

end FLT.Mazur.RelativeMarkingSections
