/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentZeroOrderedConicIntersection
public import FLT.Mazur.WeierstrassSuccessiveXConicPunctureInclusion

/-!
# Full initial ordered conic parameters meet their next lines in exactly one puncture

Restrict the complete zero-stage conic intersection to each full ordered parameter chart.
The source is the original Laurent algebra and the line projection retains its scale.
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

local notation "p₀" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicZeroPuncture c hc)))
local notation "P₁" => Iso.inv (conicFirstParameterIso (WeierstrassCurve.a₁ W₀) c ha) ≫
  conicFirstOpenImmersion (WeierstrassCurve.a₁ W₀) c
local notation "P₂" => Iso.inv (conicSecondParameterIso (WeierstrassCurve.a₁ W₀) c ha) ≫
  conicSecondOpenImmersion (WeierstrassCurve.a₁ W₀) c

/-- The full ordered first conic parameter in the actual common global stage. -/
def adjacentZeroFirstParameter := P₁ ≫ C ≫ g

/-- The first complete parameter chart meets its next line in exactly the original puncture. -/
theorem adjacentZeroFirstParameter_isPullback :
    IsPullback (ρ₁ ≫ p) p₀ G₁
      (adjacentZeroFirstParameter hπ data D j hj hk0 hk r hr) := by
  have H := adjacentZeroConicFirst_isPullback hπ data D j hj hk0 hk hjNext hkNext r hr
  rw [conicBoundaryFirst_inclusion] at H
  have T : IsPullback (𝟙 _) p₀ (p₀ ≫ P₁) P₁ :=
    IsPullback.of_horiz_isIso_mono ⟨by simp only [Category.id_comp]⟩
  simpa only [Category.id_comp, Category.assoc, adjacentZeroFirstParameter]
    using T.paste_horiz H

/-- The first ordered intersection is the original Laurent scheme, with no extra points. -/
def adjacentZeroFirstParameterPullbackIso :=
  (adjacentZeroFirstParameter_isPullback hπ data D j hj hk0 hk
    hjNext hkNext r hr).isoPullback

/-- The line projection keeps the first reciprocal scale. -/
@[reassoc] theorem adjacentZeroFirstParameterPullbackIso_line :
    (adjacentZeroFirstParameterPullbackIso hπ data D j hj hk0 hk hjNext hkNext r hr).hom ≫
      pullback.fst G₁ (adjacentZeroFirstParameter hπ data D j hj hk0 hk r hr) = ρ₁ ≫ p :=
  (adjacentZeroFirstParameter_isPullback hπ data D j hj hk0 hk
    hjNext hkNext r hr).isoPullback_hom_fst

/-- The conic projection is the original parameter puncture on the first branch. -/
@[reassoc] theorem adjacentZeroFirstParameterPullbackIso_parameter :
    (adjacentZeroFirstParameterPullbackIso hπ data D j hj hk0 hk hjNext hkNext r hr).hom ≫
      pullback.snd G₁ (adjacentZeroFirstParameter hπ data D j hj hk0 hk r hr) = p₀ :=
  (adjacentZeroFirstParameter_isPullback hπ data D j hj hk0 hk
    hjNext hkNext r hr).isoPullback_hom_snd

/-- The full ordered second conic parameter in the actual common global stage. -/
def adjacentZeroSecondParameter := P₂ ≫ C ≫ g

/-- The second complete parameter chart meets its next line in exactly the original puncture. -/
theorem adjacentZeroSecondParameter_isPullback :
    IsPullback (ρ₂ ≫ p) p₀ G₂
      (adjacentZeroSecondParameter hπ data D j hj hk0 hk r hr) := by
  have H := adjacentZeroConicSecond_isPullback hπ data D j hj hk0 hk hjNext hkNext r hr
  rw [conicBoundarySecond_inclusion] at H
  have T : IsPullback (𝟙 _) p₀ (p₀ ≫ P₂) P₂ :=
    IsPullback.of_horiz_isIso_mono ⟨by simp only [Category.id_comp]⟩
  simpa only [Category.id_comp, Category.assoc, adjacentZeroSecondParameter]
    using T.paste_horiz H

/-- The second ordered intersection is the original Laurent scheme, with no extra points. -/
def adjacentZeroSecondParameterPullbackIso :=
  (adjacentZeroSecondParameter_isPullback hπ data D j hj hk0 hk
    hjNext hkNext r hr).isoPullback

/-- The line projection keeps the second reciprocal scale. -/
@[reassoc] theorem adjacentZeroSecondParameterPullbackIso_line :
    (adjacentZeroSecondParameterPullbackIso hπ data D j hj hk0 hk hjNext hkNext r hr).hom ≫
      pullback.fst G₂ (adjacentZeroSecondParameter hπ data D j hj hk0 hk r hr) = ρ₂ ≫ p :=
  (adjacentZeroSecondParameter_isPullback hπ data D j hj hk0 hk
    hjNext hkNext r hr).isoPullback_hom_fst

/-- The conic projection is the original parameter puncture on the second branch. -/
@[reassoc] theorem adjacentZeroSecondParameterPullbackIso_parameter :
    (adjacentZeroSecondParameterPullbackIso hπ data D j hj hk0 hk hjNext hkNext r hr).hom ≫
      pullback.snd G₂ (adjacentZeroSecondParameter hπ data D j hj hk0 hk r hr) = p₀ :=
  (adjacentZeroSecondParameter_isPullback hπ data D j hj hk0 hk
    hjNext hkNext r hr).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
