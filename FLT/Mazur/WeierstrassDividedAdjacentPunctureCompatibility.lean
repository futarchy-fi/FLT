/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentNormalizedIntersection
public import FLT.Mazur.WeierstrassDividedAdjacentZeroNormalizedIntersection
public import FLT.Mazur.WeierstrassSuccessiveXConicPunctureDescent

/-!
# Adjacent compatibility detected on the two original Laurent punctures

The complete retained-chart fiber product is the conic incidence open.
Its proved open cover reduces arbitrary-target compatibility to the two
ordered puncture equations, for both positive and zero preceding depth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
  (hjNext : j + 2 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "fData" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
local notation "copen" => residueDividedConicOpenEquiv D (start + j) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "q" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (AlgEquiv.toAlgHom copen)))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "uNext" => coord W (π ^ (start + (j + 1))) π
  (Data.b3 fData) (Data.b4 fData) (Data.b6 fData) 2
local notation "A" => PrincipalOpenTensor.transitionIso K x t
  (depthOverlapEquiv W π (start + j) (Data.b3 e) (Data.b4 e) (Data.b6 e))
local notation "B" => PrincipalOpenTensor.transitionIso K x uNext
  (previousBoundaryEquiv hπ e fData)
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K j hj r hr
local notation "gNext" => olderGlobalTensorChart hπ data K (j + 1) hjNext r hr
local notation "W₀" => W.map (residue R)
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
variable (hp : 2 * (start + j + 1) < depth)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) hp
    (Data.b6 e) (Data.factor6 e))
local notation "s₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicBoundaryFirst W₀ c ha hc)))
local notation "s₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicBoundarySecond W₀ c ha hc)))
variable {Y : Scheme.{u}}
  (f : Spec (.of (WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + j)) π
    (Data.b3 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩))
    (Data.b4 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩))
    (Data.b6 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩)) (ResidueField R))) ⟶ Y)
  (fNext : Spec (.of (WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + (j + 1))) π
    (Data.b3 (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩))
    (Data.b4 (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩))
    (Data.b6 (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩)) (ResidueField R))) ⟶ Y)

section Positive
variable (hk0 : 0 < start + j)
local notation "E" => residueConicBoundaryIso D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "oldBoundary" => Iso.hom E ≫ PrincipalOpenTensor.inclusion K t
local notation "nextBoundary" => q ≫ Iso.inv B ≫ PrincipalOpenTensor.inclusion K uNext

/-- Both original ordered punctures suffice on the full positive-depth adjacent fiber product. -/
theorem adjacentRetainedNormalized_compatible_iff :
    (pullback.fst g gNext ≫ f = pullback.snd g gNext ≫ fNext) ↔
      (s₁ ≫ oldBoundary ≫ f = s₁ ≫ nextBoundary ≫ fNext) ∧
      (s₂ ≫ oldBoundary ≫ f = s₂ ≫ nextBoundary ≫ fNext) := by
  let H := adjacentRetainedNormalized_isPullback hπ data D j hj hk0 hk hjNext r hr
  have he : (pullback.fst g gNext ≫ f = pullback.snd g gNext ≫ fNext) ↔
      oldBoundary ≫ f = nextBoundary ≫ fNext := by
    rw [← cancel_epi H.isoPullback.hom]
    simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
      IsPullback.isoPullback_hom_snd]
  rw [he]
  constructor
  · intro h
    exact ⟨congrArg (fun k => s₁ ≫ k) h, congrArg (fun k => s₂ ≫ k) h⟩
  · rintro ⟨h₁, h₂⟩
    exact residueConicPunctures_hom_ext D (start + j) hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
      (Data.factor6 e) hp _ _ h₁ h₂

end Positive

section Zero
variable (hk0 : start + j = 0)
local notation "E" => zeroResidueConicBoundaryIso D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "oldBoundary" => Iso.hom E ≫ PrincipalOpenTensor.inclusion K t
local notation "nextBoundary" => q ≫ Iso.inv B ≫ PrincipalOpenTensor.inclusion K uNext

/-- Both original ordered punctures suffice on the full zero-depth adjacent fiber product. -/
theorem adjacentZeroNormalized_compatible_iff :
    (pullback.fst g gNext ≫ f = pullback.snd g gNext ≫ fNext) ↔
      (s₁ ≫ oldBoundary ≫ f = s₁ ≫ nextBoundary ≫ fNext) ∧
      (s₂ ≫ oldBoundary ≫ f = s₂ ≫ nextBoundary ≫ fNext) := by
  let H := adjacentZeroNormalized_isPullback hπ data D j hj hk0 hk hjNext r hr
  have he : (pullback.fst g gNext ≫ f = pullback.snd g gNext ≫ fNext) ↔
      oldBoundary ≫ f = nextBoundary ≫ fNext := by
    rw [← cancel_epi H.isoPullback.hom]
    simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
      IsPullback.isoPullback_hom_snd]
  rw [he]
  constructor
  · intro h
    exact ⟨congrArg (fun k => s₁ ≫ k) h, congrArg (fun k => s₂ ≫ k) h⟩
  · rintro ⟨h₁, h₂⟩
    exact residueConicPunctures_hom_ext D (start + j) hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
      (Data.factor6 e) hp _ _ h₁ h₂

end Zero

end FLT.Mazur.WeierstrassDividedDepth
