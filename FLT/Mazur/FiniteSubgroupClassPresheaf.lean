/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupIsoBaseChange

/-!
# The presheaf of finite subgroup isomorphism classes

Quotient full generalized-curve and finite-subgroup data by compatible
isomorphism. Actual base change defines the restriction maps; the canonical
comparison isomorphisms prove identity and composition in the quotient.
The cyclic and ample conditions are not imposed in this presheaf.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

/-- Compatible-isomorphism classes of rank-n subgroups on full generalized curves. -/
def finiteSubgroupClasses (S : Scheme) (n : ℕ) := Quotient (compatibleIsoSetoid S n)

/-- Restrict an isomorphism class by actual pullback of both the curve and subgroup. -/
def finiteSubgroupClassesPullback {S T : Scheme} (g : T ⟶ S) (n : ℕ) :
    finiteSubgroupClasses S n → finiteSubgroupClasses T n :=
  Quotient.map (fun a ↦ ⟨a.1.baseChange g, a.2.baseChange g⟩)
    (fun _ _ ⟨a⟩ ↦ ⟨a.baseChange g⟩)

/-- The canonical identity comparison gives identity on the quotient. -/
theorem finiteSubgroupClassesPullback_id (S : Scheme) (n : ℕ) :
    finiteSubgroupClassesPullback (𝟙 S) n = id := by
  funext x
  refine Quotient.inductionOn x fun a ↦ ?_
  exact Quotient.sound ⟨compatibleBaseChangeId a.2⟩

/-- The canonical composition comparison gives the presheaf composition law. -/
theorem finiteSubgroupClassesPullback_comp {S T U : Scheme}
    (g : T ⟶ S) (h : U ⟶ T) (n : ℕ) :
    finiteSubgroupClassesPullback (h ≫ g) n =
      finiteSubgroupClassesPullback h n ∘ finiteSubgroupClassesPullback g n := by
  funext x
  refine Quotient.inductionOn x fun a ↦ ?_
  exact Quotient.sound ⟨compatibleBaseChangeComp a.2 g h⟩

/-- The actual isomorphism-class presheaf of finite subgroup data of fixed rank. -/
def finiteSubgroupClassPresheaf (n : ℕ) : Schemeᵒᵖ ⥤ Type 1 where
  obj S := finiteSubgroupClasses S.unop n
  map f := ↾(finiteSubgroupClassesPullback f.unop n)
  map_id S := by
    ext x
    exact congrFun (finiteSubgroupClassesPullback_id S.unop n) x
  map_comp f g := by
    ext x
    exact congrFun (finiteSubgroupClassesPullback_comp f.unop g.unop n) x

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
