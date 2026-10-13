/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearScaleOneGluedConic
public import FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedEquationDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
public import FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections

public import FLT.Mazur.WeierstrassCoefficientShearAdjacentGluedBoundary
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentGluedBoundary
public import FLT.Mazur.WeierstrassDividedAdjacentRetainedTensorIntersection

/-!
# Full scale-one adjacent intersections of the original sheared atlas

The whole preceding conic incidence open identifies the actual pairwise
fiber product at every common later depth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S)
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (m : ℕ) (hm : j + 2 + m ≤ n)
include hj hjNext
local notation "d" => data (Fin.mk (j + 1) (by omega))
local notation "e" => data (Fin.mk (j + 2) (by omega))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j) * π)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 d) (Data.b4 d) (Data.b6 d) 0
local notation "v" => coord W (π ^ (start + (j + 1))) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "A" => PrincipalOpenTensor.transitionIso S x t
  (overlapEquiv W (π ^ (start + j)) π (Data.b3 d) (Data.b4 d) (Data.b6 d))
local notation "B" => PrincipalOpenTensor.transitionIso S x v (adjacentBoundaryEquiv hπ d e)
local notation "old" => coefficientShearRetainedTensorChart hπ data S r
  (j + 2 + m) hm (Fin.mk j (by omega))
local notation "next" => coefficientShearRetainedTensorChart hπ data S r
  (j + 2 + m) hm (Fin.mk (j + 1) (by omega))

variable (hs : algebraMap R S (π ^ (start + j)) = 1) (hp : algebraMap R S π = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "g3" => And.left (coefficientShearAdjacent_coefficients hπ d e S hp)
local notation "g4" => And.left (And.right (coefficientShearAdjacent_coefficients hπ d e S hp))
local notation "E" => tensorShearScaleOneConicBoundaryIso W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp g3 g4 hr
local notation "N" => coefficientShearScaleOneAdjacentConicToNext hπ d e S r hs hp hr

local notation "ciOld" => successiveCoefficientShearIso W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r
local notation "ciNext" => successiveCoefficientShearIso W (π ^ (start + (j + 1))) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) S r
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S (Data.b6 d)
local notation "inc" => PrincipalOpenTransport.inclusion (conicT (U).a₁ c)
local notation "I" => coefficientShearRetainedScaleOneTensorIso data S r (j + 2 + m) hm
  ⟨j, by omega⟩
local notation "C" => tensorShearScaleOneConicImmersion W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp g3 g4 hr
local notation "h2" => coefficientShear_a₂_zero W S r hr
local notation "G" => coefficientShearGluedIso hπ data S r (j + 2 + m) hm
local notation "atlas" => coefficientShearAtlasMap hπ data S r (j + 2 + m) hm
local notation "oldIndex" => Sum.inr (Fin.mk j (by omega))
local notation "nextIndex" => Sum.inr (Fin.mk (j + 1) (by omega))

/-- The entire conic boundary is the actual adjacent atlas pullback at any later depth. -/
theorem coefficientShearScaleOneAdjacentAtlas_isPullback :
    IsPullback (inc ≫ C ≫ (I).inv)
      (N ≫ (ciNext).inv) (atlas oldIndex) (atlas nextIndex) := by
  apply (coefficientShearScaleOneAdjacentGluedCharts_isPullback
    hπ data S r j hj hjNext m hm hs hp hr).of_iso
    (Iso.refl _) (ciOld).symm (ciNext).symm G
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
    rw [tensorShearScaleOneConicBoundaryIso_inclusion, Category.assoc]
    rfl
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
  · rw [coefficientShearRetainedTensorChart, Category.assoc,
      coefficientShearGluedIso_chart]
    rfl
  · rw [coefficientShearRetainedTensorChart, Category.assoc,
      coefficientShearGluedIso_chart]
    rfl

/-- The explicit boundary compares isomorphically to the full adjacent scheme intersection. -/
def coefficientShearScaleOneAdjacentAtlasPullbackIso :=
  (coefficientShearScaleOneAdjacentAtlas_isPullback
    hπ data S r j hj hjNext m hm hs hp hr).isoPullback

/-- The old projection is the original full conic inclusion into the retained equation. -/
theorem coefficientShearScaleOneAdjacentAtlasPullbackIso_fst :
    (coefficientShearScaleOneAdjacentAtlasPullbackIso
      hπ data S r j hj hjNext m hm hs hp hr).hom ≫
      pullback.fst (atlas oldIndex) (atlas nextIndex) =
        inc ≫ C ≫ (I).inv :=
  (coefficientShearScaleOneAdjacentAtlas_isPullback
    hπ data S r j hj hjNext m hm hs hp hr).isoPullback_hom_fst

/-- The next projection retains the full original horizontal transition. -/
@[reassoc] theorem coefficientShearScaleOneAdjacentAtlasPullbackIso_snd :
    (coefficientShearScaleOneAdjacentAtlasPullbackIso
      hπ data S r j hj hjNext m hm hs hp hr).hom ≫
      pullback.snd (atlas oldIndex) (atlas nextIndex) = N ≫ (ciNext).inv :=
  (coefficientShearScaleOneAdjacentAtlas_isPullback
    hπ data S r j hj hjNext m hm hs hp hr).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
