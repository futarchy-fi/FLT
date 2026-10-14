/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearScaleOneTerminalNodeTensorPullback
public import FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedEquationDescent
public import FLT.Mazur.WeierstrassCoefficientShearRootLaurentOverlap
public import FLT.Mazur.WeierstrassCoefficientShearTerminalEquationCharts
public import FLT.Mazur.WeierstrassCoefficientShearRetainedReconstruction
public import FLT.Mazur.WeierstrassDividedGlobalTensorIntersection
public import FLT.Mazur.WeierstrassDividedTerminalParameterOrigins
public import FLT.Mazur.WeierstrassCoefficientShearConicParameters
public import FLT.Mazur.WeierstrassCoefficientShearRootTerminalOverlap
public import FLT.Mazur.WeierstrassSuccessiveXConicPunctureInclusion
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# The full scale-one strict terminal atlas intersection

Transport the original terminal fiber product to the full strict divided and retained
equations, preserving both original overlap projections.
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
variable (hs : algebraMap R S (π ^ (start + j)) = 1) (hp : algebraMap R S π = 0)
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
local notation "N" => coefficientShearTerminalNode
  hπ data S r (j + 1) hj hsNext h3 h4 h6 hr a ha
local notation "G" => coefficientShearGluedIso hπ data S r (j + 1) hj
local notation "ψ" => tensorShearScaleOneTerminalNodeConicMap W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr h6 a ha
local notation "b" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "inc" => PrincipalOpenTransport.inclusion (conicT (U).a₁ c)
local notation "F" => tensorShearScaleOneConicBoundaryIso W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr
local notation "T" => tensorShearTerminalNodeEquiv W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hp h3 h4 hr h6 a ha

local notation "J" => Scheme.Spec.mapIso (T).toRingEquiv.toCommRingCatIso.op
local notation "cmap" => tensorShearScaleOneConicImmersion W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr
local notation "div" => (J).hom ≫ globalDividedTensorChart hπ data S (j + 1) hj
local notation "ret" => globalSuccessiveTensorChart hπ data S j hj

local notation "L" => coefficientShearTerminalEquationIso
  data S r (j + 1) hj hsNext h3 h4 h6 hr a ha
local notation "I" => coefficientShearRetainedScaleOneTensorIso data S r (j + 1) hj
  ⟨j, Nat.lt_succ_self j⟩
local notation "ci" => successiveCoefficientShearIso W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r
local notation "h2" => coefficientShear_a₂_zero W S r hr
local notation "A" => coefficientShearAtlasMap hπ data S r (j + 1) hj
local notation "retIndex" => Sum.inr (Fin.mk j (Nat.lt_succ_self j))

/-- The explicit conic-node boundary is the entire actual terminal atlas overlap. -/
theorem coefficientShearScaleOneTerminalNodeAtlas_isPullback :
    IsPullback (b ≫ (L).hom) (inc ≫ cmap ≫ (I).inv)
      (A (.inl 1)) (A retIndex) := by
  apply (coefficientShearScaleOneTerminalNodeTensor_isPullback
    hπ data S r j hj hs hp h3 h4 h6 hr a ha).of_iso
    (Iso.refl _) L (ci).symm (Iso.refl _)
  · simp only [Iso.refl_hom, Category.id_comp]
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp, Category.assoc]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id]
    have H := coefficientShearRootTerminalNode_reconstruction
      hπ data S r j hj hp h3 h4 h6 hr a ha
    rw [← coefficientShearTerminalEquationIso_chart,
      Category.assoc, coefficientShearGluedIso_chart] at H
    exact H.symm
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id]
    have H := coefficientShearRootTerminalRetained_reconstruction hπ data S r j hj
    rw [coefficientShearRetainedTensorChart, Category.assoc,
      coefficientShearGluedIso_chart] at H
    exact H.symm

/-- The localized conic identifies the full pullback of the original atlas embeddings. -/
def coefficientShearScaleOneTerminalNodeAtlasPullbackIso :=
  (coefficientShearScaleOneTerminalNodeAtlas_isPullback
    hπ data S r j hj hs hp h3 h4 h6 hr a ha).isoPullback

/-- The full overlap's divided projection is the original node boundary. -/
@[reassoc] theorem coefficientShearScaleOneTerminalNodeAtlasPullbackIso_fst :
    (coefficientShearScaleOneTerminalNodeAtlasPullbackIso
      hπ data S r j hj hs hp h3 h4 h6 hr a ha).hom ≫
      pullback.fst (A (.inl 1)) (A retIndex) = b ≫ (L).hom :=
  (coefficientShearScaleOneTerminalNodeAtlas_isPullback
    hπ data S r j hj hs hp h3 h4 h6 hr a ha).isoPullback_hom_fst

/-- The full overlap's retained projection is the entire conic boundary inclusion. -/
theorem coefficientShearScaleOneTerminalNodeAtlasPullbackIso_snd :
    (coefficientShearScaleOneTerminalNodeAtlasPullbackIso
      hπ data S r j hj hs hp h3 h4 h6 hr a ha).hom ≫
      pullback.snd (A (.inl 1)) (A retIndex) =
        inc ≫ cmap ≫ (I).inv :=
  (coefficientShearScaleOneTerminalNodeAtlas_isPullback
    hπ data S r j hj hs hp h3 h4 h6 hr a ha).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
