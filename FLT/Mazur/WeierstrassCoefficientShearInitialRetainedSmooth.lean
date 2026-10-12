/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialSmooth
public import FLT.Mazur.WeierstrassCoefficientShearRetainedReconstruction
public import FLT.Mazur.WeierstrassDividedInitialTensorIntersection

/-!
# Both original tensor embeddings on the initial retained smooth boundary

The complete common tensor boundary has the same smooth embedding from either
chart, in the original coefficient model and in the full sheared equation gluing.
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
  (S : Type) [CommRing S] [Algebra R S] (r : S)
  (h1 : 1 ≤ n) (m : ℕ) (hm : 1 + m ≤ n)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le h1))
local notation "s" => π ^ start
local notation "V" => W.map (algebraMap R S)
local notation "x" => WeierstrassDilatation.x W s (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t" => WeierstrassModificationX.t W s (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "v" => WeierstrassSuccessiveX.coord W s π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "A" => PrincipalOpenTensor.transitionIso S x t
  (overlapEquiv W s (Data.b3 d) (Data.b4 d) (Data.b6 d))
local notation "B" => PrincipalOpenTensor.transitionIso S x v (previousBoundaryEquiv hπ d e)
local notation "I" => Iso.inv A ≫ PrincipalOpenTensor.inclusion S t
local notation "J" => Iso.inv B ≫ PrincipalOpenTensor.inclusion S v
local notation "E" => coefficientShearGluedIso hπ data S r (1 + m) hm

/-- The two original tensor embeddings agree on their complete common boundary after gluing. -/
theorem coefficientShearInitialRetained_boundary :
    I ≫ coefficientShearInitialTensorChart hπ data S r (1 + m) hm =
      J ≫ coefficientShearRetainedTensorChart hπ data S r (1 + m) hm ⟨0, by omega⟩ := by
  apply (cancel_mono (E).hom).mp
  simp only [Category.assoc, coefficientShearInitialTensorChart_original,
    coefficientShearRetainedTensorChart_original hπ data S r 0 h1 m hm]
  exact (initialRetainedGlobalTensor_isPullback hπ data S h1 m hm).w

variable (hs : algebraMap R S (π ^ start) = 1)
  (h3 : algebraMap R S (Data.b3 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (h6 : algebraMap R S (Data.b6 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (W.map (algebraMap R S)).a₁ + 2 * r)
local notation "P" => tensorShearScaleOneSmoothInput W s (Data.b3 d) (Data.b4 d)
  (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) S r hs h3 h4 h6 hr a ha

/-- The retained side of the actual whole tensor boundary is the original smooth embedding. -/
theorem coefficientShearRetained_initialSmoothInput :
    J ≫ coefficientShearRetainedTensorChart hπ data S r (1 + m) hm ⟨0, by omega⟩ =
      I ≫ P ≫ coefficientShearSmoothEmbedding hπ data S r (1 + m) hm := by
  rw [← coefficientShearInitialRetained_boundary hπ data S r h1 m hm,
    coefficientShearInitialTensorChart_smoothInput hπ data S r (1 + m) hm
      hs h3 h4 h6 hr a ha]

/-- Reconstruction identifies the same retained boundary in the original coefficient model. -/
theorem olderGlobalTensorChart_initialSmoothInput :
    J ≫ olderGlobalTensorChart hπ data S 0 h1 m hm =
      I ≫ P ≫ finiteGlobalSmoothCoefficientEmbedding S hπ data (1 + m) hm := by
  have h := congrArg (· ≫ (E).hom)
    (coefficientShearRetained_initialSmoothInput hπ data S r h1 m hm hs h3 h4 h6 hr a ha)
  simpa only [Category.assoc, coefficientShearRetainedTensorChart_original hπ data S r
    0 h1 m hm, coefficientShearSmoothEmbedding_reconstruction] using h

end FLT.Mazur.WeierstrassDividedDepth
