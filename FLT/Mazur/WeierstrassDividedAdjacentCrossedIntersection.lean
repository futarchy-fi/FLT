/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentParameterIntersection
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Crossed adjacent ordered branches have empty scheme intersection

The complete first conic parameter misses the next opposite line, and conversely.
The proof uses the entire conic pullbacks and disjoint full parameter charts.
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

/-- The whole first conic parameter misses the next second line. -/
theorem adjacentRetainedFirstParameter_cross_disjoint :
    Disjoint (Set.range A₁) (Set.range G₂) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, rfl⟩ ⟨b, hb⟩
  obtain ⟨v, _, hv⟩ := Scheme.exists_preimage_of_isPullback
    (adjacentRetainedConicSecond_isPullback hπ data D j hj hk0 hk hjNext hkNext r hr)
    b (P₁ a) hb
  rw [conicBoundarySecond_inclusion] at hv
  have H := conicParameters_disjoint_of_zero W₀ c ha hc
  exact Set.disjoint_left.mp H ⟨a, rfl⟩ ⟨p₀ v, hv⟩

/-- The entire crossed first-parameter intersection is the empty scheme. -/
theorem adjacentRetainedFirstParameter_cross_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) A₁ G₂ := by
  let _ := Scheme.isEmpty_pullback A₁ G₂
    (adjacentRetainedFirstParameter_cross_disjoint hπ data D j hj hk0 hk hjNext hkNext r hr)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback A₁ G₂)))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

/-- The original crossed first-parameter fiber product is canonically empty. -/
def adjacentRetainedFirstParameterCrossPullbackIso : (∅ : Scheme) ≅ pullback A₁ G₂ :=
  (adjacentRetainedFirstParameter_cross_isPullback hπ data D j hj hk0 hk
    hjNext hkNext r hr).isoPullback

/-- The whole second conic parameter misses the next first line. -/
theorem adjacentRetainedSecondParameter_cross_disjoint :
    Disjoint (Set.range A₂) (Set.range G₁) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, rfl⟩ ⟨b, hb⟩
  obtain ⟨v, _, hv⟩ := Scheme.exists_preimage_of_isPullback
    (adjacentRetainedConicFirst_isPullback hπ data D j hj hk0 hk hjNext hkNext r hr)
    b (P₂ a) hb
  rw [conicBoundaryFirst_inclusion] at hv
  have H := conicParameters_disjoint_of_zero W₀ c ha hc
  exact Set.disjoint_left.mp H ⟨p₀ v, hv⟩ ⟨a, rfl⟩

/-- The entire crossed second-parameter intersection is the empty scheme. -/
theorem adjacentRetainedSecondParameter_cross_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) A₂ G₁ := by
  let _ := Scheme.isEmpty_pullback A₂ G₁
    (adjacentRetainedSecondParameter_cross_disjoint hπ data D j hj hk0 hk hjNext hkNext r hr)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback A₂ G₁)))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

/-- The original crossed second-parameter fiber product is canonically empty. -/
def adjacentRetainedSecondParameterCrossPullbackIso : (∅ : Scheme) ≅ pullback A₂ G₁ :=
  (adjacentRetainedSecondParameter_cross_isPullback hπ data D j hj hk0 hk
    hjNext hkNext r hr).isoPullback

end FLT.Mazur.WeierstrassDividedDepth
