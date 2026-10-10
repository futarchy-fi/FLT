/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalZeroSuccessive
public import FLT.Mazur.WeierstrassDividedFiniteTensorOverlap
public import FLT.Mazur.WeierstrassSuccessiveXZeroOverlap

/-!
# The full first horizontal overlap in the global atlas

The normalized incidence open follows the original depth transition into the
actual adjacent divided chart. The equality holds on the whole overlap.
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

/-- The full horizontal overlap agrees with the original adjacent global divided inclusion. -/
@[reassoc] theorem globalZeroSuccessive_overlap :
    (E).hom ≫ (PrincipalOpenTensor.transitionIso K x t₀ a).hom ≫
      PrincipalOpenTensor.inclusion K x ≫ globalDividedTensorChart hπ data K (j + 1) hj =
        PrincipalOpenTransport.inclusion t ≫
          globalZeroSuccessiveChart hπ data D j hj hk0 hk := by
  have hg : (PrincipalOpenTensor.transitionIso K x t₀ a).hom ≫
      PrincipalOpenTensor.inclusion K x ≫ globalDividedTensorChart hπ data K (j + 1) hj =
        PrincipalOpenTensor.inclusion K t₀ ≫ globalSuccessiveTensorChart hπ data K j hj := by
    simp only [globalDividedTensorChart, globalSuccessiveTensorChart, ← Category.assoc]
    exact congrArg (fun f => f ≫ finiteLocalTensorEmbedding hπ data K (j + 1) hj)
      (finiteTensor_depthOverlap hπ data K j hj)
  rw [hg, ← Category.assoc]
  change ((E).hom ≫ PrincipalOpenTransport.inclusion _) ≫ _ = _
  rw [zeroResidueXOpenIso_inclusion, Category.assoc]
  rfl

/-- The whole normalized overlap is an actual open immersion into the global model. -/
def globalZeroOverlapChart :=
  PrincipalOpenTransport.inclusion t ≫ globalZeroSuccessiveChart hπ data D j hj hk0 hk

instance globalZeroOverlapChart_isOpenImmersion :
    IsOpenImmersion (globalZeroOverlapChart hπ data D j hj hk0 hk) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- Its range is exactly the image of the full original horizontal principal open. -/
theorem globalZeroOverlapChart_range :
    Set.range (globalZeroOverlapChart hπ data D j hj hk0 hk) =
      globalZeroSuccessiveChart hπ data D j hj hk0 hk ''
        (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum
          (WeierstrassModificationX.FiberCoordinate (residue R W.a₁)
            (residue R (Data.b6 e))))) := by
  change Set.range ((globalZeroSuccessiveChart hπ data D j hj hk0 hk) ∘
    PrincipalOpenTransport.inclusion t) = _
  rw [Set.range_comp]
  congr 1
  exact PrimeSpectrum.localization_away_comap_range _ t

end FLT.Mazur.WeierstrassDividedDepth
