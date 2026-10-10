/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Limits

/-!
# The category of original cartesian test families

Objects retain independently supplied total spaces and pullback squares.
Morphisms retain both the actual base map and the actual total-space map.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ProperFamilyTests
variable {X S : Scheme.{0}} (f : X ⟶ S)

/-- An original test family with its specified cartesian square. -/
structure Family where
  /-- The original test base. -/
  base : Scheme.{0}
  /-- The original total space. -/
  total : Scheme.{0}
  /-- The map to the fixed total space. -/
  fst : total ⟶ X
  /-- The family structure morphism. -/
  snd : total ⟶ base
  /-- The original base map. -/
  toBase : base ⟶ S
  /-- The square is cartesian. -/
  square : IsPullback fst snd f toBase

namespace Family
variable {f}

/-- A morphism of original test families. -/
@[ext] structure Hom (A B : Family f) where
  /-- The map of test bases. -/
  base : A.base ⟶ B.base
  /-- The map of total spaces. -/
  total : A.total ⟶ B.total
  /-- The fixed-total-space triangle commutes. -/
  fst : total ≫ B.fst = A.fst
  /-- The family square commutes. -/
  snd : total ≫ B.snd = A.snd ≫ base
  /-- The fixed-base triangle commutes. -/
  over : base ≫ B.toBase = A.toBase

/-- Identity on both original schemes. -/
def Hom.id (A : Family f) : Hom A A :=
  ⟨𝟙 _, 𝟙 _, Category.id_comp _, by simp, Category.id_comp _⟩

/-- Compose both actual scheme maps. -/
def Hom.comp {A B C : Family f} (u : Hom A B) (v : Hom B C) : Hom A C :=
  ⟨u.base ≫ v.base, u.total ≫ v.total,
    by rw [Category.assoc, v.fst, u.fst],
    by rw [Category.assoc, v.snd, ← Category.assoc, u.snd, Category.assoc],
    by rw [Category.assoc, v.over, u.over]⟩

instance : Category (Family f) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp u := by ext <;> simp [Hom.id, Hom.comp]
  comp_id u := by ext <;> simp [Hom.id, Hom.comp]
  assoc u v w := by ext <;> simp [Hom.comp, Category.assoc]

/-- Forget the total space while retaining the original base scheme. -/
def baseFunctor : Family f ⥤ Scheme.{0} where
  obj A := A.base
  map u := u.base

/-- Forget the test base while retaining the original total space. -/
def totalFunctor : Family f ⥤ Scheme.{0} where
  obj A := A.total
  map u := u.total

end Family
end FLT.Mazur.ProperFamilyTests
