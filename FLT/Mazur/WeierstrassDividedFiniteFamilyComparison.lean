/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalFiniteGluing
public import FLT.Mazur.WeierstrassDividedDepthAvailability
/-!
# Finite local models are independent of unused family entries

Two coefficient families of different lengths construct the same local scheme
at each common stage. Coefficient uniqueness and induction compare the actual
exteriors and contractions, without identifying the families' index types.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] Exterior.whole initialExterior Exterior.advance
  Exterior.stepContraction
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {start n m : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (other : (i : Fin (m + 1)) → Data W π (start + i.val))

/-- Compare the constructed exteriors at any common stage. -/
theorem finiteExterior_family_heq (j : ℕ) (hj : j ≤ n) (hm : j ≤ m) :
    HEq (finiteExterior hπ data (initialExterior (data ⟨0, by omega⟩)) j hj)
      (finiteExterior hπ other (initialExterior (other ⟨0, by omega⟩)) j hm) := by
  induction j with
  | zero =>
    dsimp only [finiteExterior]
    congr 1
    exact Data.eq_of_depth hπ _ _
  | succ j ih =>
    dsimp only [finiteExterior]
    congr 1
    · exact Data.eq_of_depth hπ _ _
    · exact ih (by omega) (by omega)
    · exact Data.eq_of_depth hπ _ _

/-- The whole local model does not depend on the total family length. -/
theorem finiteModification_family_eq (j : ℕ) (hj : j ≤ n) (hm : j ≤ m) :
    finiteModification hπ data j hj = finiteModification hπ other j hm := by
  unfold finiteModification finiteWhole
  congr 1
  · exact Data.eq_of_depth hπ _ _
  · exact finiteExterior_family_heq hπ data other j hj hm

/-- The actual composite contractions agree across differently indexed families. -/
theorem finiteContraction_family_heq (j : ℕ) (hj : j ≤ n) (hm : j ≤ m) :
    HEq (finiteContraction hπ data (initialExterior (data ⟨0, by omega⟩)) j hj)
      (finiteContraction hπ other (initialExterior (other ⟨0, by omega⟩)) j hm) := by
  induction j with
  | zero =>
    dsimp only [finiteContraction]
    exact (eqToHom_heq_id_dom _ _ (finiteModification_family_eq hπ data other 0 hj hm)).symm.trans
      (eqToHom_heq_id_cod _ _ (finiteModification_family_eq hπ data other 0 hj hm))
  | succ j ih =>
    dsimp only [finiteContraction, finiteStep]
    apply heq_comp (finiteModification_family_eq hπ data other (j + 1) hj hm)
      (finiteModification_family_eq hπ data other j (by omega) (by omega))
      (finiteModification_family_eq hπ data other 0 (by omega) (by omega))
    · congr 1
      · exact Data.eq_of_depth hπ _ _
      · exact finiteExterior_family_heq hπ data other j (by omega) (by omega)
      · exact Data.eq_of_depth hπ _ _
    · exact ih (by omega) (by omega)

attribute [local irreducible] initialToAffine

/-- The affine cubic contraction is preserved by the family comparison. -/
theorem finiteToAffine_family_heq (j : ℕ) (hj : j ≤ n) (hm : j ≤ m) :
    HEq (finiteToAffine hπ data j hj) (finiteToAffine hπ other j hm) := by
  unfold finiteToAffine
  apply heq_comp (finiteModification_family_eq hπ data other j hj hm)
    (finiteModification_family_eq hπ data other 0 (by omega) (by omega)) rfl
  · exact finiteContraction_family_heq hπ data other j hj hm
  · congr 1
    exact Data.eq_of_depth hπ _ _

/-- The explicit scheme identification commutes with the original affine map. -/
@[reassoc] theorem finiteModification_family_toAffine
    (j : ℕ) (hj : j ≤ n) (hm : j ≤ m) :
    eqToHom (finiteModification_family_eq hπ data other j hj hm) ≫
      finiteToAffine hπ other j hm = finiteToAffine hπ data j hj := by
  apply eq_of_heq
  exact (eqToHom_comp_heq _ _).trans
    (finiteToAffine_family_heq hπ data other j hj hm).symm

end FLT.Mazur.WeierstrassDividedDepth
