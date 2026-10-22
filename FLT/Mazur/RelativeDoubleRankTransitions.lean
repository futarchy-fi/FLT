/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDoubleRankUniversal
public import FLT.Mazur.RelativeDoubleRankRecovery

/-!
# Transitions between independent full rank orders

Increasing the two orders constructs a canonical map of full coefficient
schemes. The maps preserve the original coefficient and both rank coordinates,
and form a directed system. No comparison arrow between different ranks is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (x y : B ⟶ S) (n m : ℕ)

/-- Increase both full ideal-power orders, retaining the original coefficient map. -/
def doubleRankTransition {r s r' s' : ℕ} (hr : r ≤ r') (hs : s ≤ s') :
    doubleRankThickening E x y n m r s ⟶ doubleRankThickening E x y n m r' s' :=
  doubleRankLift E x y n m r' s' (doubleRankMap E x y n m r s)
    (doubleRankFirst E x y n m r s ≫ rankStageTransition E n hr)
    (doubleRankSecond E x y n m r s ≫ rankStageTransition E m hs)
    (by rw [Category.assoc, rankStageTransition_map, doubleRankFirst_map])
    (by rw [Category.assoc, rankStageTransition_map, doubleRankSecond_map])

/-- Every original coefficient is retained by the order transition. -/
@[reassoc (attr := simp)]
theorem doubleRankTransition_map {r s r' s' : ℕ} (hr : r ≤ r') (hs : s ≤ s') :
    doubleRankTransition E x y n m hr hs ≫ doubleRankMap E x y n m r' s' =
      doubleRankMap E x y n m r s :=
  doubleRankLift_map _ _ _ _ _ _ _ _ _ _ _ _

/-- The first full coordinate follows its actual ideal-power transition. -/
@[reassoc (attr := simp)]
theorem doubleRankTransition_first {r s r' s' : ℕ} (hr : r ≤ r') (hs : s ≤ s') :
    doubleRankTransition E x y n m hr hs ≫ doubleRankFirst E x y n m r' s' =
      doubleRankFirst E x y n m r s ≫ rankStageTransition E n hr :=
  doubleRankLift_first _ _ _ _ _ _ _ _ _ _ _ _

/-- The second full coordinate follows its independent ideal-power transition. -/
@[reassoc (attr := simp)]
theorem doubleRankTransition_second {r s r' s' : ℕ} (hr : r ≤ r') (hs : s ≤ s') :
    doubleRankTransition E x y n m hr hs ≫ doubleRankSecond E x y n m r' s' =
      doubleRankSecond E x y n m r s ≫ rankStageTransition E m hs :=
  doubleRankLift_second _ _ _ _ _ _ _ _ _ _ _ _

/-- The order transition at a fixed pair is the identity on the entire scheme. -/
@[simp] theorem doubleRankTransition_refl (r s : ℕ) :
    doubleRankTransition E x y n m (le_refl r) (le_refl s) = 𝟙 _ := by
  apply (cancel_mono (doubleRankMap E x y n m r s)).mp
  rw [doubleRankTransition_map, Category.id_comp]

/-- Independent order increases compose exactly, without a choice of coordinates. -/
@[reassoc (attr := simp)]
theorem doubleRankTransition_comp {r s r' s' r'' s'' : ℕ}
    (hr : r ≤ r') (hs : s ≤ s') (hr' : r' ≤ r'') (hs' : s' ≤ s'') :
    doubleRankTransition E x y n m hr hs ≫ doubleRankTransition E x y n m hr' hs' =
      doubleRankTransition E x y n m (hr.trans hr') (hs.trans hs') := by
  apply (cancel_mono (doubleRankMap E x y n m r'' s'')).mp
  rw [Category.assoc, doubleRankTransition_map, doubleRankTransition_map,
    doubleRankTransition_map]

instance doubleRankTransition_mono {r s r' s' : ℕ} (hr : r ≤ r') (hs : s ≤ s') :
    Mono (doubleRankTransition E x y n m hr hs) :=
  mono_of_mono_fac (doubleRankTransition_map E x y n m hr hs)

end FLT.Mazur.RelativeOrderedTuples
