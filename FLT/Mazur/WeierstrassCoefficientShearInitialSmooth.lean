/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearSmoothUnique
public import FLT.Mazur.WeierstrassModificationXTensorSmoothInput

/-!
# The actual initial tensor chart is in the original smooth orbit at scale one

The original chart is reconstructed through the coefficient gluing and then
identified with the smooth embedding by both of its actual pullback legs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type) [CommRing S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "s" => π ^ start
local notation "V" => W.map (algebraMap R S)
local notation "T" => ScalarExtension W s (Data.b3 d) (Data.b4 d) (Data.b6 d) S
local notation "E" => coefficientShearGluedIso hπ data S r j hj
local notation "J" => incidenceCoefficientShearIso W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r

/-- The original initial tensor equation embedded through the actual sheared chart. -/
def coefficientShearInitialTensorChart : Spec (.of T) ⟶
    coefficientShearGlued hπ data S r j hj :=
  (J).inv ≫ coefficientShearGluedChart hπ data S r j hj (.inl 2)

/-- Reconstruction recovers the independently constructed original initial tensor chart. -/
@[reassoc] theorem coefficientShearInitialTensorChart_original :
    coefficientShearInitialTensorChart hπ data S r j hj ≫ (E).hom =
      globalInitialTensorChart hπ data S j hj := by
  rw [coefficientShearInitialTensorChart, Category.assoc, coefficientShearGluedIso_chart]
  change (J).inv ≫ (J).hom ≫ globalInitialTensorChart hπ data S j hj = _
  rw [Iso.inv_hom_id_assoc]

variable (hs : algebraMap R S (π ^ start) = 1)
  (h3 : algebraMap R S (Data.b3 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (h6 : algebraMap R S (Data.b6 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (W.map (algebraMap R S)).a₁ + 2 * r)
local notation "P" => tensorShearScaleOneSmoothInput W s (Data.b3 d) (Data.b4 d)
  (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) S r hs h3 h4 h6 hr a ha

/-- The entire original initial chart is the actual smooth coefficient embedding. -/
theorem globalInitialTensorChart_smoothInput :
    globalInitialTensorChart hπ data S j hj =
      P ≫ finiteGlobalSmoothCoefficientEmbedding S hπ data j hj := by
  apply finiteGlobal_eq_smoothCoefficientEmbedding
  · rw [globalInitialTensorChart_structure, tensorShearScaleOneSmoothInput_structure]
    rfl
  · rw [globalInitialTensorChart_toCurve, tensorShearScaleOneSmoothInput_original]

/-- The full initial sheared tensor embedding agrees with its actual original smooth input. -/
theorem coefficientShearInitialTensorChart_smoothInput :
    coefficientShearInitialTensorChart hπ data S r j hj =
      P ≫ coefficientShearSmoothEmbedding hπ data S r j hj := by
  apply (cancel_mono (E).hom).mp
  rw [coefficientShearInitialTensorChart_original, Category.assoc,
    coefficientShearSmoothEmbedding_reconstruction]
  exact globalInitialTensorChart_smoothInput hπ data S r j hj hs h3 h4 h6 hr a ha

end FLT.Mazur.WeierstrassDividedDepth
