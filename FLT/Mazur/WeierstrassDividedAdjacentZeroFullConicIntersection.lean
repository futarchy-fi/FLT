/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentZeroNormalizedIntersection

/-!
# The whole zero-stage conic intersects the next chart in its incidence open

The zero-stage normalized adjacent square restricts to the original closed conic immersion.
Both its full boundary and the next inverse horizontal projection are retained.
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
local notation "E" => zeroResidueConicBoundaryIso D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

open WeierstrassModificationX
local notation "W₀" => W.map (residue R)
local notation "c" => residue R (Data.b6 e)
local notation "C₀" => ConicCoordinate (WeierstrassCurve.a₁ W₀) c
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap C₀ (MiddleConicOpen W₀ c)))
local notation "C" => zeroResidueConicImmersion D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

/-- The complete conic and complete next chart meet in exactly the original incidence open. -/
theorem adjacentZeroFullConic_isPullback :
    IsPullback (q ≫ (B).inv ≫ PrincipalOpenTensor.inclusion K uNext) i gNext (C ≫ g) := by
  have H := adjacentZeroNormalized_isPullback hπ data D j hj hk0 hk hjNext r hr
  rw [zeroResidueConicBoundaryIso_inclusion] at H
  have T : IsPullback (𝟙 _) i (i ≫ C) C :=
    IsPullback.of_horiz_isIso_mono ⟨by simp only [Category.id_comp]⟩
  simpa only [Category.id_comp] using T.paste_horiz H.flip

/-- The conic intersection has its original full boundary as the source scheme. -/
def adjacentZeroFullConicPullbackIso :=
  (adjacentZeroFullConic_isPullback hπ data D j hj hk0 hk hjNext r hr).isoPullback

/-- The next-chart projection retains the entire inverse horizontal transition. -/
@[reassoc] theorem adjacentZeroFullConicPullbackIso_next :
    (adjacentZeroFullConicPullbackIso hπ data D j hj hk0 hk hjNext r hr).hom ≫
      pullback.fst gNext (C ≫ g) = q ≫ (B).inv ≫ PrincipalOpenTensor.inclusion K uNext :=
  (adjacentZeroFullConic_isPullback hπ data D j hj hk0 hk hjNext r hr).isoPullback_hom_fst

/-- The conic projection is exactly its original incidence-open inclusion. -/
@[reassoc] theorem adjacentZeroFullConicPullbackIso_conic :
    (adjacentZeroFullConicPullbackIso hπ data D j hj hk0 hk hjNext r hr).hom ≫
      pullback.snd gNext (C ≫ g) = i :=
  (adjacentZeroFullConic_isPullback hπ data D j hj hk0 hk hjNext r hr).isoPullback_hom_snd

/-- No point outside the conic incidence open enters the adjacent retained chart. -/
theorem adjacentZeroFullConic_preimage : (C ≫ g) ⁻¹' Set.range gNext = Set.range i := by
  have H := adjacentZeroFullConic_isPullback hπ data D j hj hk0 hk hjNext r hr
  ext z
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨p, _, hp⟩ := Scheme.exists_preimage_of_isPullback H w z hw
    exact ⟨p, hp⟩
  · rintro ⟨p, rfl⟩
    exact ⟨(q ≫ (B).inv ≫ PrincipalOpenTensor.inclusion K uNext) p,
      congrArg (fun morphism => morphism p) H.w⟩

end FLT.Mazur.WeierstrassDividedDepth
