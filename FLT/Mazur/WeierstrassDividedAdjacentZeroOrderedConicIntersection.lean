/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedConicHorizontalIntersectionAllDepths
public import FLT.Mazur.WeierstrassDividedAdjacentZeroFullConicIntersection
public import FLT.Mazur.WeierstrassDividedOlderGlobalMiddleComponents

/-!
# Full zero-stage intersections with the two ordered retained lines

Each line meets the preceding full conic in exactly its corresponding puncture.
The two Laurent projections retain their original reciprocal scales.
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
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
  (hjNext : j + 2 ≤ n) (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)
  (r : ℕ) (hr : j + 2 + r ≤ n)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "fData" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
local notation "W₀" => W.map (residue R)
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "s₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicBoundaryFirst W₀ c ha hc)))
local notation "s₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicBoundarySecond W₀ c ha hc)))
local notation "copen" => residueDividedConicOpenEquiv D (start + j) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "q" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (AlgEquiv.toAlgHom copen)))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "uNext" => coord W (π ^ (start + (j + 1))) π
  (Data.b3 fData) (Data.b4 fData) (Data.b6 fData) 2
local notation "B" => PrincipalOpenTensor.transitionIso K x uNext
  (previousBoundaryEquiv hπ e fData)
local notation "LNext" => residueLineToHorizontal D (start + (j + 1)) (by omega) hkNext
  (Data.b3 fData) (Data.b4 fData) (Data.b6 fData) (Data.factor3 fData) (Data.factor4 fData)
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
local notation "ρ₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (tangent)⁻¹)))
local notation "ρ₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (-tangent)⁻¹)))
local notation "p" => ProjectiveLine.overlapLeft K

local notation "L" => residueSuccessiveLineImmersion D (start + (j + 1)) (by omega) hkNext
  (Data.b3 fData) (Data.b4 fData) (Data.b6 fData) (Data.factor3 fData) (Data.factor4 fData)

open WeierstrassModificationX
local notation "C₀" => ConicCoordinate (WeierstrassCurve.a₁ W₀) c
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap C₀ (MiddleConicOpen W₀ c)))
local notation "C" => zeroResidueConicImmersion D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K j hj r hr
local notation "G₁" => olderGlobalMiddleFirstLine hπ data D (j + 1) hjNext r hr (by omega) hkNext
local notation "G₂" => olderGlobalMiddleSecondLine hπ data D (j + 1) hjNext r hr (by omega) hkNext

/-- The whole next first line meets the whole retained conic only in its ordered puncture. -/
theorem adjacentZeroConicFirst_isPullback :
    IsPullback (ρ₁ ≫ p) (s₁ ≫ i) G₁ (C ≫ g) :=
  (adjacentConicFirstHorizontal_isPullback_anyDepth hπ data D j hj hk
    hjNext hkNext).flip.paste_vert
    (adjacentZeroFullConic_isPullback hπ data D j hj hk0 hk hjNext r hr)

/-- The full first-line intersection is the original Laurent puncture. -/
def adjacentZeroConicFirstPullbackIso :=
  (adjacentZeroConicFirst_isPullback hπ data D j hj hk0 hk hjNext hkNext r hr).isoPullback

/-- The first line projection keeps its original scaled reciprocal parameter. -/
@[reassoc] theorem adjacentZeroConicFirstPullbackIso_line :
    (adjacentZeroConicFirstPullbackIso hπ data D j hj hk0 hk hjNext hkNext r hr).hom ≫
      pullback.fst G₁ (C ≫ g) = ρ₁ ≫ p :=
  (adjacentZeroConicFirst_isPullback hπ data D j hj hk0 hk
    hjNext hkNext r hr).isoPullback_hom_fst

/-- The first conic projection is the original puncture followed by inclusion. -/
@[reassoc] theorem adjacentZeroConicFirstPullbackIso_conic :
    (adjacentZeroConicFirstPullbackIso hπ data D j hj hk0 hk hjNext hkNext r hr).hom ≫
      pullback.snd G₁ (C ≫ g) = s₁ ≫ i :=
  (adjacentZeroConicFirst_isPullback hπ data D j hj hk0 hk
    hjNext hkNext r hr).isoPullback_hom_snd

/-- The whole next opposite line meets the whole retained conic only in its ordered puncture. -/
theorem adjacentZeroConicSecond_isPullback :
    IsPullback (ρ₂ ≫ p) (s₂ ≫ i) G₂ (C ≫ g) :=
  (adjacentConicSecondHorizontal_isPullback_anyDepth hπ data D j hj hk
    hjNext hkNext).flip.paste_vert
    (adjacentZeroFullConic_isPullback hπ data D j hj hk0 hk hjNext r hr)

/-- The full opposite-line intersection is the original Laurent puncture. -/
def adjacentZeroConicSecondPullbackIso :=
  (adjacentZeroConicSecond_isPullback hπ data D j hj hk0 hk hjNext hkNext r hr).isoPullback

/-- The opposite line projection keeps its original scaled reciprocal parameter. -/
@[reassoc] theorem adjacentZeroConicSecondPullbackIso_line :
    (adjacentZeroConicSecondPullbackIso hπ data D j hj hk0 hk hjNext hkNext r hr).hom ≫
      pullback.fst G₂ (C ≫ g) = ρ₂ ≫ p :=
  (adjacentZeroConicSecond_isPullback hπ data D j hj hk0 hk
    hjNext hkNext r hr).isoPullback_hom_fst

/-- The opposite conic projection is the original puncture followed by inclusion. -/
@[reassoc] theorem adjacentZeroConicSecondPullbackIso_conic :
    (adjacentZeroConicSecondPullbackIso hπ data D j hj hk0 hk hjNext hkNext r hr).hom ≫
      pullback.snd G₂ (C ≫ g) = s₂ ≫ i :=
  (adjacentZeroConicSecond_isPullback hπ data D j hj hk0 hk
    hjNext hkNext r hr).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
