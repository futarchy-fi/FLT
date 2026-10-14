/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialLineContraction
public import FLT.Mazur.WeierstrassDividedGlobalFiniteProper
public import FLT.Mazur.ProjectiveLineValuationExtension

/-!
# Complete independent normalization of the root-sheared exterior

Properness extends the actual root-sheared incidence line across infinity.
The extension keeps the entire affine line and is uniquely determined by it.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open ProjectiveLine WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
  (hs : algebraMap R S (π ^ start) = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "L" => coefficientShearInitialLine hπ data S r j hj hs h3 h4 hr
local notation "p" => coefficientShearGluedStructure hπ data S r j hj

/-- Properness constructs a unique full normalization from the independent incidence chart. -/
theorem coefficientShearInitialCompleteNormalization_existsUnique :
    ∃! f : scheme S ⟶ coefficientShearGlued hπ data S r j hj,
      f ≫ p = toBase S ∧ left S ≫ f = L := by
  let _ : IsProper p := by
    unfold coefficientShearGluedStructure
    infer_instance
  apply existsUnique_left_extension S (toBase S) p L
  rw [coefficientShearInitialLine_structure, left_toBase]
  rfl

/-- The independently constructed complete root-sheared exterior, including infinity. -/
@[irreducible] def coefficientShearInitialCompleteNormalization :
    scheme S ⟶ coefficientShearGlued hπ data S r j hj :=
  (coefficientShearInitialCompleteNormalization_existsUnique
    hπ data S r j hj hs h3 h4 hr).choose
local notation "N" => coefficientShearInitialCompleteNormalization hπ data S r j hj hs h3 h4 hr

/-- The complete normalization preserves the actual coefficient field. -/
@[reassoc] theorem coefficientShearInitialCompleteNormalization_structure : N ≫ p = toBase S := by
  rw [coefficientShearInitialCompleteNormalization]
  exact (coefficientShearInitialCompleteNormalization_existsUnique
    hπ data S r j hj hs h3 h4 hr).choose_spec.1.1

/-- The extension retains the whole independently constructed affine incidence line. -/
@[reassoc] theorem coefficientShearInitialCompleteNormalization_left : left S ≫ N = L := by
  rw [coefficientShearInitialCompleteNormalization]
  exact (coefficientShearInitialCompleteNormalization_existsUnique
    hπ data S r j hj hs h3 h4 hr).choose_spec.1.2

/-- The original affine line and coefficient map determine the full exterior. -/
theorem coefficientShearInitialCompleteNormalization_unique
    (f : scheme S ⟶ coefficientShearGlued hπ data S r j hj)
    (hf : f ≫ p = toBase S) (hl : left S ≫ f = L) : f = N := by
  rw [coefficientShearInitialCompleteNormalization]
  exact (coefficientShearInitialCompleteNormalization_existsUnique
    hπ data S r j hj hs h3 h4 hr).choose_spec.2 f ⟨hf, hl⟩

/-- The entire original affine cubic contraction survives the full normalization. -/
@[reassoc] theorem coefficientShearInitialCompleteNormalization_left_toCurve :
    left S ≫ N ≫ coefficientShearGluedProjection hπ data S r j hj ≫
        finiteGlobalContraction hπ data j hj =
      Spec.map (CommRingCat.ofHom
        (originalShearIncidenceNormalization W (π ^ start)
          (Data.b3 (data ⟨0, Nat.zero_lt_succ n⟩))
          (Data.b4 (data ⟨0, Nat.zero_lt_succ n⟩))
          (Data.b6 (data ⟨0, Nat.zero_lt_succ n⟩)) S r hs h3 h4 hr
          (Data.factor3 (data ⟨0, Nat.zero_lt_succ n⟩))
          (Data.factor4 (data ⟨0, Nat.zero_lt_succ n⟩))
          (Data.factor6 (data ⟨0, Nat.zero_lt_succ n⟩))).toRingHom) ≫
        WeierstrassIntegralChart.integralCurveChart W 2 := by
  rw [coefficientShearInitialCompleteNormalization_left_assoc,
    coefficientShearInitialLine_toCurve]

end FLT.Mazur.WeierstrassDividedDepth
