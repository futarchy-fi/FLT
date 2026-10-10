/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyTestCategory
public import FLT.Mazur.RelativePicardPresheaf

/-!
# Canonical cartesian families on the category of test bases

The usual fiber-product family gives a functor into original test families.
Its morphisms retain the same actual total-space maps as the relative Picard presheaf.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ProperFamilyTests
variable {X S : Scheme.{0}} (f : X ⟶ S)

/-- The independently constructed canonical pullback family of a scheme over the base. -/
def canonicalFamily (T : Over S) : Family f where
  base := T.left
  total := Limits.pullback f T.hom
  fst := Limits.pullback.fst f T.hom
  snd := Limits.pullback.snd f T.hom
  toBase := T.hom
  square := IsPullback.of_hasPullback f T.hom

/-- The canonical morphism retains the actual total map of the relative Picard presheaf. -/
def canonicalFamilyMap {T U : Over S} (u : T ⟶ U) : canonicalFamily f T ⟶ canonicalFamily f U :=
  ⟨u.left, SchemePicard.relativeTotalMap f u, SchemePicard.relativeTotalMap_fst f u,
    SchemePicard.relativeTotalMap_snd f u, u.w⟩

/-- Canonical pullback families form a functor on all schemes over the fixed base. -/
def canonicalFamilyFunctor : Over S ⥤ Family f where
  obj := canonicalFamily f
  map := canonicalFamilyMap f
  map_id T := by
    apply Family.Hom.ext
    · rfl
    · exact SchemePicard.relativeTotalMap_id f T
  map_comp u v := by
    apply Family.Hom.ext
    · rfl
    · exact SchemePicard.relativeTotalMap_comp f u v

/-- The functor's actual total-space map agrees with the original relative Picard construction. -/
lemma canonicalFamilyFunctor_total {T U : Over S} (u : T ⟶ U) :
    ((canonicalFamilyFunctor f).map u).total = SchemePicard.relativeTotalMap f u := rfl

/-- Forget the original total space, retaining the actual scheme over the fixed base. -/
def originalBaseFunctor : Family f ⥤ Over S where
  obj A := Over.mk A.toBase
  map u := Over.homMk u.base u.over
  map_id A := by ext; rfl
  map_comp u v := by ext; rfl

end FLT.Mazur.ProperFamilyTests
