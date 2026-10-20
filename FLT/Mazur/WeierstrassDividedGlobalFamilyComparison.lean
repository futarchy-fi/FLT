/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteFamilyComparison
public import FLT.Mazur.WeierstrassDividedGlobalFiniteProper

/-!
# Global finite models across differently indexed coefficient families

The local comparison preserves the unchanged boundary, so the actual global
pushouts and their original cubic and coefficient maps agree at every common
stage. This supplies transport without equating different family lengths.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteModification finiteToAffine SchemeUnchangedOpen.lift
  finiteYBoundary SchemeOpenReplacement.contraction
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n m : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (other : (i : Fin (m + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n) (hm : j ≤ m)

/-- The unchanged original boundary agrees in both local constructions. -/
theorem finiteYBoundary_family_heq :
    HEq (finiteYBoundary hπ data j hj) (finiteYBoundary hπ other j hm) := by
  unfold finiteYBoundary
  congr! 1
  · exact finiteModification_family_eq hπ data other j hj hm
  · exact finiteToAffine_family_heq hπ data other j hj hm

/-- The actual global pushouts agree at each common stage. -/
theorem finiteGlobalModel_family_eq :
    finiteGlobalModel hπ data j hj = finiteGlobalModel hπ other j hm := by
  unfold finiteGlobalModel
  congr! 1
  · exact finiteModification_family_eq hπ data other j hj hm
  · exact finiteYBoundary_family_heq hπ data other j hj hm

/-- The original projective cubic contraction is unchanged by the comparison. -/
theorem finiteGlobalContraction_family_heq :
    HEq (finiteGlobalContraction hπ data j hj)
      (finiteGlobalContraction hπ other j hm) := by
  unfold finiteGlobalContraction
  apply heq_comp (finiteGlobalModel_family_eq hπ data other j hj hm) rfl rfl
  · congr! 1
    · exact finiteModification_family_eq hπ data other j hj hm
    · exact finiteYBoundary_family_heq hπ data other j hj hm
    · exact finiteToAffine_family_heq hπ data other j hj hm
  · rfl

/-- The global coefficient structures also agree. -/
theorem finiteGlobalStructure_family_heq :
    HEq (finiteGlobalStructure hπ data j hj) (finiteGlobalStructure hπ other j hm) := by
  unfold finiteGlobalStructure
  exact heq_comp (finiteGlobalModel_family_eq hπ data other j hj hm) rfl rfl
    (finiteGlobalContraction_family_heq hπ data other j hj hm) HEq.rfl

/-- The explicit global identification retains the original cubic contraction. -/
@[reassoc] theorem finiteGlobalModel_family_contraction :
    eqToHom (finiteGlobalModel_family_eq hπ data other j hj hm) ≫
      finiteGlobalContraction hπ other j hm = finiteGlobalContraction hπ data j hj := by
  apply eq_of_heq
  exact (eqToHom_comp_heq _ _).trans
    (finiteGlobalContraction_family_heq hπ data other j hj hm).symm

/-- The explicit global identification is over the original coefficient scheme. -/
@[reassoc] theorem finiteGlobalModel_family_structure :
    eqToHom (finiteGlobalModel_family_eq hπ data other j hj hm) ≫
      finiteGlobalStructure hπ other j hm = finiteGlobalStructure hπ data j hj := by
  apply eq_of_heq
  exact (eqToHom_comp_heq _ _).trans
    (finiteGlobalStructure_family_heq hπ data other j hj hm).symm

end FLT.Mazur.WeierstrassDividedDepth
