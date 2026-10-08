/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.DirectSum.Basic

/-!
# Direct sums of additive complexes in original coordinates

The terms are actual finite-support families; every differential and degree
inclusion uses the original component map. No homology comparison is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped DirectSum

universe u v

namespace FLT.Mazur.AdditiveComplexDirectSum

variable {ι : Type v} {c : ComplexShape ι}
  (K : ℕ → HomologicalComplex AddCommGrpCat.{u} c)

/-- The complex of finite-support families with the original component differentials. -/
def complex : HomologicalComplex AddCommGrpCat.{u} c where
  X q := AddCommGrpCat.of (⨁ n, (K n).X q)
  d p q := AddCommGrpCat.ofHom (DirectSum.map fun n ↦ ((K n).d p q).hom)
  shape p q h := by
    apply ConcreteCategory.hom_ext
    intro x
    apply DFinsupp.ext
    intro n
    change (K n).d p q (x n) = 0
    rw [(K n).shape p q h]
    rfl
  d_comp_d' p q r _ _ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply DFinsupp.ext
    intro n
    exact ConcreteCategory.congr_hom ((K n).d_comp_d p q r) (x n)

/-- The actual differential retains each original coefficient. -/
lemma d_apply (p q : ι) (x : ⨁ n, (K n).X p) (n : ℕ) :
    DFinsupp.toFun (show ⨁ n, (K n).X q from (complex K).d p q x) n = (K n).d p q (x n) := rfl

/-- Differentiating one original degree stays in that degree. -/
lemma d_of (p q : ι) (n : ℕ) (x : (K n).X p) :
    (complex K).d p q (DirectSum.of (fun k ↦ (K k).X p) n x) =
      DirectSum.of (fun k ↦ (K k).X q) n ((K n).d p q x) :=
  DirectSum.map_of _ _ _

/-- The original component inclusion is a morphism of complexes. -/
def inclusion (n : ℕ) : K n ⟶ complex K where
  f q := AddCommGrpCat.ofHom (DirectSum.of (fun k ↦ (K k).X q) n)
  comm' p q _ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact d_of K p q n x

/-- Each component map of the inclusion is exactly the original direct-sum injection. -/
lemma inclusion_f (n : ℕ) (q : ι) (x : (K n).X q) :
    (inclusion K n).f q x = DirectSum.of (fun k ↦ (K k).X q) n x := rfl

end FLT.Mazur.AdditiveComplexDirectSum
