/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalMiddleComponents
public import FLT.Mazur.WeierstrassDividedOlderGlobalSections
public import FLT.Mazur.WeierstrassSuccessiveXResidueConicBoundaryGeometry

/-!
# The entire conic boundary in every retained global stage

The original full incidence boundary retains its exact component map after
all later modifications. Its square remains cartesian in the actual global
model, with the original conic and tensor transition projections.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 e)
local notation "g" => olderGlobalTensorChart hπ data K j hj r hr
open WeierstrassModificationX
local notation "a" => residue R W.a₁
local notation "ha" => D.a₁_unit.map (residue R)
local notation "C" => olderGlobalMiddleConic hπ data D j hj r hr hk0 hk
local notation "W₀" => W.map (residue R)
local notation "B" => MiddleConicOpen W₀ c
local notation "C₀" => ConicCoordinate (WeierstrassCurve.a₁ W₀) c
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap C₀ B))
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "E" => residueConicBoundaryIso D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

/-- The entire original incidence-open conic in any retained global stage. -/
def olderGlobalConicBoundary := i ≫ C

/-- The original transition chart map is exactly the retained conic boundary map. -/
@[reassoc] theorem olderGlobalConicBoundary_transition :
    (E).hom ≫ PrincipalOpenTensor.inclusion K t ≫ g =
      olderGlobalConicBoundary hπ data D j hj r hr hk0 hk :=
  residueConicBoundaryIso_inclusion_assoc D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) g

/-- The entire transition boundary is the full pullback of the original retained conic. -/
theorem olderGlobalConicBoundary_isPullback :
    IsPullback (E).hom i (PrincipalOpenTensor.inclusion K t ≫ g) C := by
  have H := residueConicBoundary_isPullback D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _ g H.cone H.isLimit)

/-- The full retained conic intersection keeps the original conic boundary as its source. -/
def olderGlobalConicBoundaryPullbackIso : Spec (.of B) ≅
    pullback (PrincipalOpenTensor.inclusion K t ≫ g) C :=
  (olderGlobalConicBoundary_isPullback hπ data D j hj r hr hk0 hk).isoPullback

/-- The retained intersection comparison preserves the whole original transition open. -/
@[reassoc] theorem olderGlobalConicBoundaryPullbackIso_transition :
    (olderGlobalConicBoundaryPullbackIso hπ data D j hj r hr hk0 hk).hom ≫
      pullback.fst (PrincipalOpenTensor.inclusion K t ≫ g) C = (E).hom :=
  (olderGlobalConicBoundary_isPullback hπ data D j hj r hr hk0 hk).isoPullback_hom_fst

/-- The retained intersection comparison preserves its full original conic inclusion. -/
@[reassoc] theorem olderGlobalConicBoundaryPullbackIso_conic :
    (olderGlobalConicBoundaryPullbackIso hπ data D j hj r hr hk0 hk).hom ≫
      pullback.snd (PrincipalOpenTensor.inclusion K t ≫ g) C = i :=
  (olderGlobalConicBoundary_isPullback hπ data D j hj r hr hk0 hk).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
