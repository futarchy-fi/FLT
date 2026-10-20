/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteSmoothChart
public import FLT.Mazur.WeierstrassDividedLowerData

/-!
# Promote a supplied divided chart without replacing its coefficients

Uniqueness of the actual coefficient quotients identifies any supplied datum
at the same numerical depth with the family datum. The whole relative smooth
chart then embeds in a chosen later stage with its original contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n k : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (i : ℕ) (hi : i ≤ n)
  (d : Data W π k) (hk : start + i = k) (j : ℕ) (hij : i ≤ j) (hj : j ≤ n)
local notation "A" => WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "s" => Spec.map (CommRingCat.ofHom (algebraMap R A))
local notation "V" => (s).smoothLocus
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

/-- Embed the whole supplied divided smooth chart in the chosen common finite stage. -/
def finiteSuppliedDividedSmoothChart : (V).toScheme ⟶ (U).toScheme := by
  subst k
  have hd := Data.unique hπ d (data ⟨i, Nat.lt_succ_of_le hi⟩)
  subst d
  exact finitePromotedDividedSmoothChart hπ data i hi j hij hj

instance finiteSuppliedDividedSmoothChart_open :
    IsOpenImmersion (finiteSuppliedDividedSmoothChart hπ data i hi d hk j hij hj) := by
  subst k
  have hd := Data.unique hπ d (data ⟨i, Nat.lt_succ_of_le hi⟩)
  subst d
  unfold finiteSuppliedDividedSmoothChart
  infer_instance

/-- The promoted chart retains the exact original cubic map of the supplied datum. -/
@[reassoc] theorem finiteSuppliedDividedSmoothChart_contraction :
    finiteSuppliedDividedSmoothChart hπ data i hi d hk j hij hj ≫ (U).ι ≫
        finiteGlobalContraction hπ data j hj = (V).ι ≫ toCurve d := by
  subst k
  have hd := Data.unique hπ d (data ⟨i, Nat.lt_succ_of_le hi⟩)
  subst d
  exact finitePromotedDividedSmoothChart_contraction hπ data i hi j hij hj

/-- The supplied smooth chart keeps its original coefficient structure after promotion. -/
@[reassoc] theorem finiteSuppliedDividedSmoothChart_structure :
    finiteSuppliedDividedSmoothChart hπ data i hi d hk j hij hj ≫ (U).ι ≫ base =
      (V).ι ≫ s := by
  subst k
  have hd := Data.unique hπ d (data ⟨i, Nat.lt_succ_of_le hi⟩)
  subst d
  exact finitePromotedDividedSmoothChart_structure hπ data i hi j hij hj

end FLT.Mazur.WeierstrassDividedDepth
