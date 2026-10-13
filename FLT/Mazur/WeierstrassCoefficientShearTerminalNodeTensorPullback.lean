/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearTerminalBoundaryGeometry
public import FLT.Mazur.WeierstrassCoefficientShearTerminalNode
public import FLT.Mazur.WeierstrassCoefficientShearRetainedReconstruction
public import FLT.Mazur.WeierstrassDividedGlobalTensorIntersection
public import FLT.Mazur.WeierstrassDividedTerminalParameterOrigins
public import FLT.Mazur.WeierstrassCoefficientShearConicParameters
public import FLT.Mazur.WeierstrassCoefficientShearRootTerminalOverlap
public import FLT.Mazur.WeierstrassSuccessiveXConicPunctureInclusion
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# The complete strict terminal node intersection

The original localized conic is the full fiber product of the strict terminal node
chart and the last original retained tensor chart.
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
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (hs : algebraMap R S (π ^ (start + j)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (h6 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S (Data.b6 d)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "hsNext" => show algebraMap R S (π ^ (start + (j + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, hp, mul_zero]
local notation "conic" => coefficientShearRetainedConic hπ data S r (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j)) hs hp h3 h4 hr
local notation "N" => coefficientShearTerminalNode
  hπ data S r (j + 1) hj hsNext h3 h4 h6 hr a ha
local notation "G" => coefficientShearGluedIso hπ data S r (j + 1) hj
local notation "ψ" => tensorShearTerminalNodeConicMap W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr h6 a ha
local notation "b" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "inc" => PrincipalOpenTransport.inclusion (conicT (U).a₁ c)
local notation "F" => tensorShearConicBoundaryIso W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr
local notation "T" => tensorShearTerminalNodeEquiv W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hp h3 h4 hr h6 a ha

local notation "J" => Scheme.Spec.mapIso (T).toRingEquiv.toCommRingCatIso.op
local notation "cmap" => tensorShearConicImmersion W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr
local notation "div" => (J).hom ≫ globalDividedTensorChart hπ data S (j + 1) hj
local notation "ret" => globalSuccessiveTensorChart hπ data S j hj

/-- The entire localized conic is the strict terminal node/retained tensor fiber product. -/
theorem coefficientShearTerminalNodeTensor_isPullback :
    IsPullback b (inc ≫ cmap) div ret := by
  apply (globalTensor_depthOverlap_isPullback hπ data S j hj).of_iso'
    F J (Iso.refl _) (Iso.refl _)
  · simpa only [Category.assoc] using
      (tensorShearTerminalNodeConicMap_boundary
        W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d)
        S r hs hp h3 h4 hr h6 a ha).symm
  · simpa only [Iso.refl_hom, Category.comp_id] using
      tensorShearConicBoundaryIso_inclusion W (π ^ (start + j)) π
        (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr
  · simp only [Iso.refl_hom, Category.comp_id]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- The comparison is an isomorphism onto the actual full scheme overlap. -/
def coefficientShearTerminalNodeTensorPullbackIso :=
  (coefficientShearTerminalNodeTensor_isPullback
    hπ data S r j hj hs hp h3 h4 h6 hr a ha).isoPullback

/-- Its first projection retains the original node boundary map. -/
@[reassoc] theorem coefficientShearTerminalNodeTensorPullbackIso_fst :
    (coefficientShearTerminalNodeTensorPullbackIso
      hπ data S r j hj hs hp h3 h4 h6 hr a ha).hom ≫ pullback.fst div ret = b :=
  (coefficientShearTerminalNodeTensor_isPullback
    hπ data S r j hj hs hp h3 h4 h6 hr a ha).isoPullback_hom_fst

/-- Its second projection retains the original full conic inclusion. -/
@[reassoc] theorem coefficientShearTerminalNodeTensorPullbackIso_snd :
    (coefficientShearTerminalNodeTensorPullbackIso
      hπ data S r j hj hs hp h3 h4 h6 hr a ha).hom ≫ pullback.snd div ret = inc ≫ cmap :=
  (coefficientShearTerminalNodeTensor_isPullback
    hπ data S r j hj hs hp h3 h4 h6 hr a ha).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
