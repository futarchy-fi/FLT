/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentCrossedIntersection
public import FLT.Mazur.WeierstrassDividedResidueAtlasExtension
public import FLT.Mazur.PullbackOverlapBaseChange

/-!
# Ordered adjacent parameter intersections after coefficient extension

The entire Laurent intersections remain cartesian in the actual extended global
model. Their projections retain both reciprocal line coordinates and conic punctures.
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
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
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
local notation "C" => residueSuccessiveConicImmersion D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K j hj r hr
local notation "G₁" => olderGlobalMiddleFirstLine hπ data D (j + 1) hjNext r hr (by omega) hkNext
local notation "G₂" => olderGlobalMiddleSecondLine hπ data D (j + 1) hjNext r hr (by omega) hkNext

local notation "p₀" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicZeroPuncture c hc)))
local notation "P₁" => Iso.inv (conicFirstParameterIso (WeierstrassCurve.a₁ W₀) c ha) ≫
  conicFirstOpenImmersion (WeierstrassCurve.a₁ W₀) c
local notation "P₂" => Iso.inv (conicSecondParameterIso (WeierstrassCurve.a₁ W₀) c ha) ≫
  conicSecondOpenImmersion (WeierstrassCurve.a₁ W₀) c

local notation "A₁" => adjacentRetainedFirstParameter hπ data D j hj hk0 hk r hr
local notation "A₂" => adjacentRetainedSecondParameter hπ data D j hj hk0 hk r hr

variable (S : Type u) [CommRing S] [Algebra R S] [Algebra (ResidueField R) S]
  [IsScalarTower R (ResidueField R) S]
local notation "ext" => globalResidueExtensionMap hπ data S (j + 2 + r) hr
local notation "O₁" => (ρ₁ ≫ p) ≫ G₁
local notation "O₂" => (ρ₂ ≫ p) ≫ G₂
local notation "H₁" => adjacentRetainedFirstParameter_isPullback hπ data D j hj hk0 hk
  hjNext hkNext r hr
local notation "H₂" => adjacentRetainedSecondParameter_isPullback hπ data D j hj hk0 hk
  hjNext hkNext r hr

/-- The full extended first Laurent boundary maps to the actual next line. -/
def adjacentExtendedFirstBoundaryLine : pullback ext O₁ ⟶ pullback ext G₁ :=
  PullbackOverlapBaseChange.first ext

/-- The same full extended first boundary maps to its retained parameter chart. -/
def adjacentExtendedFirstBoundaryParameter : pullback ext O₁ ⟶ pullback ext A₁ :=
  PullbackOverlapBaseChange.second H₁ ext

/-- Extension retains the original first reciprocal Laurent line coordinate. -/
@[reassoc] theorem adjacentExtendedFirstBoundaryLine_original :
    adjacentExtendedFirstBoundaryLine hπ data D j hk0 hjNext hkNext r hr S ≫
      pullback.snd ext G₁ = pullback.snd ext O₁ ≫ (ρ₁ ≫ p) :=
  PullbackOverlapBaseChange.first_snd ext

/-- Extension retains the original first conic parameter puncture. -/
@[reassoc] theorem adjacentExtendedFirstBoundaryParameter_original :
    adjacentExtendedFirstBoundaryParameter hπ data D j hj hk0 hk hjNext hkNext r hr S ≫
      pullback.snd ext A₁ = pullback.snd ext O₁ ≫ p₀ :=
  PullbackOverlapBaseChange.second_snd H₁ ext

/-- The complete extended first intersection is the coefficient pullback of its Laurent open. -/
theorem adjacentExtendedFirstParameter_isPullback :
    IsPullback (adjacentExtendedFirstBoundaryLine hπ data D j hk0 hjNext hkNext r hr S)
      (adjacentExtendedFirstBoundaryParameter hπ data D j hj hk0 hk hjNext hkNext r hr S)
      (pullback.fst ext G₁) (pullback.fst ext A₁) :=
  PullbackOverlapBaseChange.isPullback H₁ ext

/-- The actual extended first-branch fiber product retains its full original boundary. -/
def adjacentExtendedFirstParameterPullbackIso : pullback ext O₁ ≅
    pullback (pullback.fst ext G₁) (pullback.fst ext A₁) :=
  (adjacentExtendedFirstParameter_isPullback hπ data D j hj hk0 hk
    hjNext hkNext r hr S).isoPullback

/-- The full extended second Laurent boundary maps to the actual next line. -/
def adjacentExtendedSecondBoundaryLine : pullback ext O₂ ⟶ pullback ext G₂ :=
  PullbackOverlapBaseChange.first ext

/-- The same full extended second boundary maps to its retained parameter chart. -/
def adjacentExtendedSecondBoundaryParameter : pullback ext O₂ ⟶ pullback ext A₂ :=
  PullbackOverlapBaseChange.second H₂ ext

/-- Extension retains the original second reciprocal Laurent line coordinate. -/
@[reassoc] theorem adjacentExtendedSecondBoundaryLine_original :
    adjacentExtendedSecondBoundaryLine hπ data D j hk0 hjNext hkNext r hr S ≫
      pullback.snd ext G₂ = pullback.snd ext O₂ ≫ (ρ₂ ≫ p) :=
  PullbackOverlapBaseChange.first_snd ext

/-- Extension retains the original second conic parameter puncture. -/
@[reassoc] theorem adjacentExtendedSecondBoundaryParameter_original :
    adjacentExtendedSecondBoundaryParameter hπ data D j hj hk0 hk hjNext hkNext r hr S ≫
      pullback.snd ext A₂ = pullback.snd ext O₂ ≫ p₀ :=
  PullbackOverlapBaseChange.second_snd H₂ ext

/-- The complete extended second intersection is the coefficient pullback of its Laurent open. -/
theorem adjacentExtendedSecondParameter_isPullback :
    IsPullback (adjacentExtendedSecondBoundaryLine hπ data D j hk0 hjNext hkNext r hr S)
      (adjacentExtendedSecondBoundaryParameter hπ data D j hj hk0 hk hjNext hkNext r hr S)
      (pullback.fst ext G₂) (pullback.fst ext A₂) :=
  PullbackOverlapBaseChange.isPullback H₂ ext

/-- The actual extended second-branch fiber product retains its full original boundary. -/
def adjacentExtendedSecondParameterPullbackIso : pullback ext O₂ ≅
    pullback (pullback.fst ext G₂) (pullback.fst ext A₂) :=
  (adjacentExtendedSecondParameter_isPullback hπ data D j hj hk0 hk
    hjNext hkNext r hr S).isoPullback

end FLT.Mazur.WeierstrassDividedDepth
