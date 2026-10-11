/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalStepOriginal
public import FLT.Mazur.WeierstrassDividedGlobalSuccessiveCover

/-!
# The full unchanged preceding exterior in the whole successor

Transport the retained exterior pullback through the existing reassociation
isomorphism and paste it with the global local-chart pullback.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "E" => finiteExterior hπ data
  (initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))) j (Nat.le_of_succ_le hj)
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + j))
  (π * (Data.b3 e)) (π * (Data.b4 e)) (π ^ 2 * (Data.b6 e))
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)


/-- The preceding exterior chart in the whole preceding finite model. -/
def finitePrecedingExteriorChart : (E).carrier ⟶
    finiteGlobalModel hπ data j (Nat.le_of_succ_le hj) :=
  (E).exteriorChart ≫ finiteLocalChart hπ data j (Nat.le_of_succ_le hj)

instance finitePrecedingExteriorChart_isOpenImmersion :
    IsOpenImmersion (finitePrecedingExteriorChart hπ data j hj) := by
  unfold finitePrecedingExteriorChart
  infer_instance

/-- The retained successor input has precisely the preceding exterior contraction. -/
@[reassoc] theorem finiteSuccessiveRetainedChart_step :
    finiteSuccessiveRetainedChart hπ data j hj ≫ finiteGlobalStep hπ data j hj =
      finitePrecedingExteriorChart hπ data j hj := by
  rw [finiteSuccessiveRetainedChart, Category.assoc, Category.assoc, finiteGlobalStep_local]
  change _ ≫ ((E).advanceIso hπ e).inv ≫ (E).stepContraction hπ e ≫ _ = _
  rw [← Exterior.advanceIso_contraction, Category.assoc, Iso.inv_hom_id_assoc,
    Exterior.localReplacement_inl_contraction_assoc]
  rfl

/-- The old exterior is the entire inverse image of that open under the existing global step. -/
theorem finiteGlobalStep_exterior_isPullback :
    IsPullback (𝟙 (E).carrier) (finiteSuccessiveRetainedChart hπ data j hj)
      (finitePrecedingExteriorChart hπ data j hj) (finiteGlobalStep hπ data j hj) := by
  have H : IsPullback (𝟙 (E).carrier)
      (pushout.inl (E).attach (localBoundary hπ d e) ≫ ((E).advanceIso hπ e).inv)
      (E).exteriorChart ((E).stepContraction hπ e) := by
    apply ((E).localReplacement_exterior_isPullback hπ e).of_iso
      (Iso.refl _) (Iso.refl _) ((E).advanceIso hπ e).symm (Iso.refl _)
    · simp
    · simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp]
    · simp
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
      rw [← Exterior.advanceIso_contraction, Iso.inv_hom_id_assoc]
  simpa only [finiteSuccessiveRetainedChart, finitePrecedingExteriorChart,
    Category.assoc] using H.paste_vert (finiteGlobalStep_local_isPullback hπ data j hj)

/-- At the first step the retained original input is the genuine x-direction chart. -/
@[reassoc] theorem firstRetainedChart_contraction (hn : 1 ≤ n) :
    finiteSuccessiveRetainedChart hπ data 0 hn ≫ finiteGlobalContraction hπ data 1 hn =
      WeierstrassModificationX.toCurve W (π ^ (start + 0))
        (data ⟨0, Nat.zero_lt_succ n⟩).b3 (data ⟨0, Nat.zero_lt_succ n⟩).b4
        (data ⟨0, Nat.zero_lt_succ n⟩).b6 (data ⟨0, Nat.zero_lt_succ n⟩).factor3
        (data ⟨0, Nat.zero_lt_succ n⟩).factor4 (data ⟨0, Nat.zero_lt_succ n⟩).factor6 := by
  rw [← finiteGlobalStep_contraction hπ data 0 hn, finiteSuccessiveRetainedChart_step_assoc]
  rw [finitePrecedingExteriorChart, Category.assoc, finiteLocalChart_contraction]
  dsimp only [finiteExterior, finiteToCurve, finiteContraction, finiteModification, finiteWhole]
  rw [Category.id_comp]
  exact initialToCurve_exterior (data ⟨0, Nat.zero_lt_succ n⟩)

end FLT.Mazur.WeierstrassDividedDepth
