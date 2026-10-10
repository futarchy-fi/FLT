/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalZeroOverlap
public import FLT.Mazur.WeierstrassDividedGlobalTensorIntersection

/-!
# The full cartesian first horizontal intersection in the global atlas

The normalized incidence localization is the whole intersection with the
adjacent divided chart, as schemes and as point sets in the projective model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "t" => WeierstrassModificationX.fiberT (residue R W.a₁) (residue R (Data.b6 e))
local notation "t₀" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "a" => depthOverlapEquiv W π (start + j) (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "E" => zeroResidueXOpenIso D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)


/-- The full first normalized horizontal overlap is cartesian in the actual global atlas. -/
theorem globalZeroSuccessive_overlap_isPullback :
    IsPullback ((E).hom ≫ (PrincipalOpenTensor.transitionIso K x t₀ a).hom ≫
      PrincipalOpenTensor.inclusion K x) (PrincipalOpenTransport.inclusion t)
      (globalDividedTensorChart hπ data K (j + 1) hj)
      (globalZeroSuccessiveChart hπ data D j hj hk0 hk) := by
  exact (zeroResidueXOpenIso_isPullback D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)).paste_horiz
      (globalTensor_depthOverlap_isPullback hπ data K j hj)

/-- The complete divided-chart preimage is the original horizontal principal open. -/
theorem globalZeroSuccessive_divided_preimage :
    globalZeroSuccessiveChart hπ data D j hj hk0 hk ⁻¹'
      Set.range (globalDividedTensorChart hπ data K (j + 1) hj) =
        Set.range (PrincipalOpenTransport.inclusion t) := by
  have H := globalZeroSuccessive_overlap_isPullback hπ data D j hj hk0 hk
  ext z
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨p, _, hp⟩ := Scheme.exists_preimage_of_isPullback H w z hw
    exact ⟨p, hp⟩
  · rintro ⟨p, rfl⟩
    exact ⟨((E).hom ≫ (PrincipalOpenTensor.transitionIso K x t₀ a).hom ≫
      PrincipalOpenTensor.inclusion K x) p, congrArg (fun f => f p) H.w⟩

/-- The displayed normalized overlap covers exactly the intersection of the full global charts. -/
theorem globalZeroOverlapChart_intersection :
    Set.range (globalZeroOverlapChart hπ data D j hj hk0 hk) =
      Set.range (globalZeroSuccessiveChart hπ data D j hj hk0 hk) ∩
        Set.range (globalDividedTensorChart hπ data K (j + 1) hj) := by
  change Set.range ((globalZeroSuccessiveChart hπ data D j hj hk0 hk) ∘
    PrincipalOpenTransport.inclusion t) = _
  rw [Set.range_comp, ← globalZeroSuccessive_divided_preimage hπ data D j hj hk0 hk,
    Set.image_preimage_eq_inter_range, Set.inter_comm]

end FLT.Mazur.WeierstrassDividedDepth
