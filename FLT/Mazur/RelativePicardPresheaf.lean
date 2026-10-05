/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePicardQuotient
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The relative Picard presheaf

The value on T over S is Pic(X ×[S] T) modulo the pullback of Pic(T).
Actual fiber-product morphisms supply the restriction maps and functor laws.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Limits

universe u

namespace FLT.Mazur.SchemePicard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The total space map induced by a morphism of base schemes over S. -/
def relativeTotalMap {T U : Over S} (g : T ⟶ U) :
    Limits.pullback f T.hom ⟶ Limits.pullback f U.hom :=
  Limits.pullback.lift (Limits.pullback.fst _ _)
    (Limits.pullback.snd _ _ ≫ g.left) (by
      rw [Category.assoc, Over.w g]
      exact Limits.pullback.condition)

/-- The total space map commutes with projection to the variable base. -/
@[reassoc (attr := simp)]
theorem relativeTotalMap_snd {T U : Over S} (g : T ⟶ U) :
    relativeTotalMap f g ≫ Limits.pullback.snd f U.hom =
      Limits.pullback.snd f T.hom ≫ g.left :=
  Limits.pullback.lift_snd _ _ _

/-- The total space map leaves the fixed factor unchanged. -/
@[reassoc (attr := simp)]
theorem relativeTotalMap_fst {T U : Over S} (g : T ⟶ U) :
    relativeTotalMap f g ≫ Limits.pullback.fst f U.hom =
      Limits.pullback.fst f T.hom :=
  Limits.pullback.lift_fst _ _ _

/-- Identity on the variable base induces identity on the total space. -/
@[simp]
theorem relativeTotalMap_id (T : Over S) : relativeTotalMap f (𝟙 T) = 𝟙 _ := by
  apply Limits.pullback.hom_ext <;> simp

/-- Maps of the variable base compose on the actual fiber products. -/
theorem relativeTotalMap_comp {T U V : Over S} (g : T ⟶ U) (h : U ⟶ V) :
    relativeTotalMap f (g ≫ h) = relativeTotalMap f g ≫ relativeTotalMap f h := by
  apply Limits.pullback.hom_ext <;> simp [Category.assoc]

/-- The relative class map associated to a base morphism. -/
def relativeBaseMap {T U : Over S} (g : T ⟶ U) :
    RelativePic (Limits.pullback.snd f U.hom) →*
      RelativePic (Limits.pullback.snd f T.hom) :=
  relativeMap _ _ (relativeTotalMap f g) g.left (relativeTotalMap_snd f g).symm

/-- On representatives the presheaf map is sheaf pullback along the total space map. -/
@[simp]
theorem relativeBaseMap_class {T U : Over S} (g : T ⟶ U)
    (a : Pic (Limits.pullback f U.hom)) :
    relativeBaseMap f g (relativeClass (Limits.pullback.snd f U.hom) a) =
      relativeClass (Limits.pullback.snd f T.hom) (pullback (relativeTotalMap f g) a) := rfl

/-- The relative Picard presheaf with values in commutative groups. -/
def relativePresheaf : (Over S)ᵒᵖ ⥤ CommGrpCat where
  obj T := CommGrpCat.of (RelativePic (Limits.pullback.snd f T.unop.hom))
  map g := CommGrpCat.ofHom (relativeBaseMap f g.unop)
  map_id T := by
    apply CommGrpCat.Hom.ext
    apply MonoidHom.ext
    intro a
    obtain ⟨a, rfl⟩ := relativeClass_surjective (Limits.pullback.snd f T.unop.hom) a
    change relativeBaseMap f (𝟙 T.unop) (relativeClass _ a) = relativeClass _ a
    simp
  map_comp {T U V} g h := by
    apply CommGrpCat.Hom.ext
    apply MonoidHom.ext
    intro a
    obtain ⟨a, rfl⟩ := relativeClass_surjective
      (Limits.pullback.snd f T.unop.hom) a
    change relativeBaseMap f (g ≫ h).unop (relativeClass _ a) =
      relativeBaseMap f h.unop (relativeBaseMap f g.unop (relativeClass _ a))
    simp only [relativeBaseMap_class, unop_comp, relativeTotalMap_comp, pullback_comp]

end FLT.Mazur.SchemePicard
