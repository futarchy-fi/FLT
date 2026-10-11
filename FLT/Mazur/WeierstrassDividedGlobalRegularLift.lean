/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalStepOriginal
public import FLT.Mazur.RegularCenterGluedLift

/-!
# Regular-center lifts into the actual whole successor

A proved principal output center constructs a map into the normalized Rees
scheme and then the whole successor. The exact global step is retained.
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


variable {S : Type u} [CommRing S]
  (φ : WeierstrassDilatation.Coordinate W (π ^ (start + j))
    (π * (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3)
    (π * (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4)
    (π ^ 2 * (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6) →+* S) (a : S)
  (hI : (WeierstrassSuccessiveX.modificationCenter W (π ^ (start + j)) π
    (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4
    (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6).map φ = Ideal.span {a}) (ha : IsRegular a)

/-- Insert the regular-center Rees lift into the existing whole finite successor. -/
irreducible_def finiteGlobalRegularLift : Spec (.of S) ⟶
    finiteGlobalModel hπ data (j + 1) hj :=
  RegularCenter.gluedLift I φ a hI ha
    (WeierstrassSuccessiveRees.centerGenerators W (π ^ (start + j)) π (e).b3 (e).b4 (e).b6)
    (WeierstrassSuccessiveRees.centerGenerators_mem W (π ^ (start + j)) π (e).b3 (e).b4 (e).b6)
    (WeierstrassSuccessiveRees.centerGenerators_span W (π ^ (start + j)) π (e).b3 (e).b4 (e).b6) ≫
    (WeierstrassSuccessiveRees.modificationProjIso W (π ^ (start + j)) π
      (e).b3 (e).b4 (e).b6 hπ).inv ≫
    pushout.inr (E).attach (localBoundary hπ d e) ≫ ((E).advanceIso hπ e).inv ≫
    finiteLocalChart hπ data (j + 1) hj

/-- The constructed lift contracts to exactly its prescribed normalized output. -/
@[reassoc] theorem finiteGlobalRegularLift_step :
    finiteGlobalRegularLift hπ data j hj φ a hI ha ≫ finiteGlobalStep hπ data j hj =
      Spec.map (CommRingCat.ofHom φ) ≫ finiteNormalizedChart hπ data j hj := by
  rw [finiteGlobalRegularLift_def, Category.assoc, Category.assoc, Category.assoc,
    Category.assoc, finiteGlobalStep_local]
  change _ ≫ _ ≫ _ ≫ ((E).advanceIso hπ e).inv ≫
    (E).stepContraction hπ e ≫ _ = _
  rw [← Exterior.advanceIso_contraction, Category.assoc, Iso.inv_hom_id_assoc,
    Exterior.localReplacement_inr_contraction_assoc]
  change _ ≫ _ ≫ (WeierstrassSuccessiveX.contraction _ _ _ _ _ _ ≫ _) ≫ _ ≫ _ = _
  rw [← WeierstrassSuccessiveRees.modificationProjIso_contraction W
    (π ^ (start + j)) π (e).b3 (e).b4 (e).b6 hπ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc,
    RegularCenter.gluedLift_contraction_assoc, finiteNormalizedChart]
  rfl

/-- Any other lift with these regular output coordinates is the constructed one. -/
theorem finiteGlobalRegularLift_unique
    (b : Spec (.of S) ⟶ finiteGlobalModel hπ data (j + 1) hj)
    (hb : b ≫ finiteGlobalStep hπ data j hj =
      Spec.map (CommRingCat.ofHom φ) ≫ finiteNormalizedChart hπ data j hj) :
    b = finiteGlobalRegularLift hπ data j hj φ a hI ha :=
  finiteGlobalStep_regular_center_ext hπ data j hj φ a hI ha b _ hb
    (finiteGlobalRegularLift_step hπ data j hj φ a hI ha)

end FLT.Mazur.WeierstrassDividedDepth
