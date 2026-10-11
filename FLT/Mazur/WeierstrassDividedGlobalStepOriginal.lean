/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalSuccessiveCharts
public import FLT.Mazur.WeierstrassDividedExteriorOriginalOpen

/-!
# Unchanged center opens and uniqueness in the whole global step

The full local-chart pullback pastes with the unchanged normalized center
opens. Regular principalization therefore detects equality of arbitrary
lifts into the whole finite successor, including flat restrictions of the
constructed local action maps.
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


/-- The existing local step is the full pullback over the preceding global local chart. -/
theorem finiteGlobalStep_local_isPullback :
    IsPullback (finiteStep hπ data
        (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj)
      (finiteLocalChart hπ data (j + 1) hj)
      (finiteLocalChart hπ data j (Nat.le_of_succ_le hj)) (finiteGlobalStep hπ data j hj) :=
  SchemeOpenReplacement.isPullback_inr (affineBoundaryToY W)
    (finiteYBoundary hπ data j (Nat.le_of_succ_le hj))
    (finiteYBoundary hπ data (j + 1) hj)
    (finiteStep hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj)
    (finiteYBoundary_step hπ data j hj)

/-- The global step retains the full inverse image of the original infinity chart. -/
theorem finiteGlobalStep_infinity_isPullback :
    IsPullback (𝟙 (chartScheme W 1)) (finiteInfinityChart hπ data (j + 1) hj)
      (finiteInfinityChart hπ data j (Nat.le_of_succ_le hj)) (finiteGlobalStep hπ data j hj) :=
  SchemeOpenReplacement.isPullback_inl (affineBoundaryToY W)
    (finiteYBoundary hπ data j (Nat.le_of_succ_le hj))
    (finiteYBoundary hπ data (j + 1) hj)
    (finiteStep hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj)
    (finiteYBoundary_step hπ data j hj) (finiteYBoundary_step_preimage hπ data j hj)

variable
  (f : WeierstrassDilatation.Coordinate W (π ^ (start + j))
    (π * (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3)
    (π * (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4)
    (π ^ 2 * (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6))
  (hf : f ∈ WeierstrassSuccessiveX.modificationCenter W (π ^ (start + j)) π
    (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3
    (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4
    (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6)

/-- The actual unchanged center principal open inside the whole global successor. -/
def finiteGlobalStepOriginal : Spec (.of (Localization.Away f)) ⟶
    finiteGlobalModel hπ data (j + 1) hj :=
  (E).stepOriginal hπ e f hf ≫ finiteLocalChart hπ data (j + 1) hj

/-- The displayed center principal open is the entire global-step inverse image. -/
theorem finiteGlobalStepOriginal_isPullback :
    IsPullback (𝟙 _) (finiteGlobalStepOriginal hπ data j hj f hf)
      (PrincipalAffineRefinement.inclusion f ≫ finiteNormalizedChart hπ data j hj)
      (finiteGlobalStep hπ data j hj) := by
  simpa only [finiteGlobalStepOriginal, finiteNormalizedChart, originalTarget,
    Category.assoc] using
    ((E).stepOriginal_isPullback hπ e f hf).paste_vert
      (finiteGlobalStep_local_isPullback hπ data j hj)

/-- A regular principalized successive center separates arbitrary lifts into the whole model. -/
theorem finiteGlobalStep_regular_center_ext {S : Type u} [CommRing S]
    (φ : B →+* S) (a : S) (hI : (I).map φ = Ideal.span {a}) (ha : IsRegular a)
    (u v : Spec (.of S) ⟶ finiteGlobalModel hπ data (j + 1) hj)
    (hu : u ≫ finiteGlobalStep hπ data j hj =
      Spec.map (CommRingCat.ofHom φ) ≫ finiteNormalizedChart hπ data j hj)
    (hv : v ≫ finiteGlobalStep hπ data j hj =
      Spec.map (CommRingCat.ofHom φ) ≫ finiteNormalizedChart hπ data j hj) : u = v := by
  apply RegularCenter.separated_lift_ext I φ a hI ha
    (WeierstrassSuccessiveRees.centerGenerators W (π ^ (start + j)) π (e).b3 (e).b4 (e).b6)
    (WeierstrassSuccessiveRees.centerGenerators_mem W (π ^ (start + j)) π
      (e).b3 (e).b4 (e).b6)
    (WeierstrassSuccessiveRees.centerGenerators_span W (π ^ (start + j)) π
      (e).b3 (e).b4 (e).b6)
    (finiteGlobalStep hπ data j hj) (finiteNormalizedChart hπ data j hj)
    (fun i => finiteGlobalStepOriginal hπ data j hj _
      (WeierstrassSuccessiveRees.centerGenerators_mem W (π ^ (start + j)) π
        (e).b3 (e).b4 (e).b6 i))
    (fun i => finiteGlobalStepOriginal_isPullback hπ data j hj _ _) u v hu hv

end FLT.Mazur.WeierstrassDividedDepth
