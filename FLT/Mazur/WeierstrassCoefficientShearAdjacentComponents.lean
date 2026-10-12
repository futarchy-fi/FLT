/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearAdjacentGluedIntersections
public import FLT.Mazur.WeierstrassCoefficientShearConicParameters
public import FLT.Mazur.WeierstrassConicZeroAffineParameter
public import FLT.Mazur.ProjectiveLineScaledReciprocalGluing
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentGluedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentGluedFullConic

/-!
# Complete adjacent projective components in the actual sheared coefficient model

Glue both full conic parameters to their actual next retained lines using
signed reciprocal transitions. The coefficient field need not split the original integral model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial
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
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "e" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
variable (hs : algebraMap R S (π ^ (start + j)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
include h3 h4
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "hsNext" => coefficientShearAdjacent_scale S hp (k := start + j)
local notation "g3" => And.left (coefficientShearAdjacent_coefficients hπ d e S hp)
local notation "g4" => And.left (And.right (coefficientShearAdjacent_coefficients hπ d e S hp))
local notation "gc" => And.right (And.right (coefficientShearAdjacent_coefficients hπ d e S hp))
local notation "c" => algebraMap R S (Data.b6 d)
local notation "p" => Spec.map (CommRingCat.ofHom
  (Polynomial.toLaurent : Polynomial S →+* S[T;T⁻¹]))

variable (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "b₁" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (conicBoundaryFirst U c hu gc)))
local notation "b₂" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (conicBoundarySecond U c hu gc)))
local notation "ρ₁" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso
    (AlgEquiv.toRingEquiv (PolygonScaledReciprocal.equiv (a⁻¹)))))
local notation "ρ₂" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso
    (AlgEquiv.toRingEquiv (PolygonScaledReciprocal.equiv ((-a)⁻¹)))))
local notation "conic" => coefficientShearRetainedConic hπ data S r (j + 2 + m) hm
  (Fin.mk j (by omega)) hs hp g3 g4 hr
local notation "inc" => PrincipalOpenTransport.inclusion
  (conicT (WeierstrassCurve.a₁ U) c)
local notation "line" => coefficientShearRetainedLine hπ data S r (j + 2 + m) hm
  (Fin.mk (j + 1) (by omega)) hsNext hp h3 h4 hr

local notation "E" => conicZeroAffineIso c gc
local notation "F₁" => (E).hom ≫ coefficientConicFirstParameter (U).a₁ c hu conic
local notation "F₂" => (E).hom ≫ coefficientConicSecondParameter (U).a₁ c hu conic
local notation "L₁" => line 0 (middle_first_root U)
local notation "L₂" => line (-(U).a₁) (middle_second_root U)

/-- The full first conic parameter and next line have the original signed reciprocal overlap. -/
theorem coefficientShearAdjacentFirstComponent_overlap :
    ProjectiveLine.overlapLeft S ≫ F₁ =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.reciprocal a⁻¹).toRingHom) ≫
        ProjectiveLine.overlapLeft S ≫ L₁ := by
  have H := (coefficientShearAdjacentGluedFirstFull_isPullback
    hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha).w
  rw [Category.assoc] at H
  erw [conicBoundaryFirst_inclusion_assoc] at H
  rw [coefficientConicFirstParameter, ← Category.assoc, conicZeroAffineIso_puncture]
  have hρ : (ρ₁).hom = Spec.map
      (CommRingCat.ofHom (PolygonScaledReciprocal.reciprocal a⁻¹).toRingHom) := rfl
  rw [hρ] at H
  simpa only [Category.assoc, ProjectiveLine.overlapLeft] using H

/-- The full opposite parameter retains the negative reciprocal tangent scale. -/
theorem coefficientShearAdjacentSecondComponent_overlap :
    ProjectiveLine.overlapLeft S ≫ F₂ =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.reciprocal (-a)⁻¹).toRingHom) ≫
        ProjectiveLine.overlapLeft S ≫ L₂ := by
  have H := (coefficientShearAdjacentGluedSecondFull_isPullback
    hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha).w
  rw [Category.assoc] at H
  erw [conicBoundarySecond_inclusion_assoc] at H
  rw [coefficientConicSecondParameter, ← Category.assoc, conicZeroAffineIso_puncture]
  have hρ : (ρ₂).hom = Spec.map
      (CommRingCat.ofHom (PolygonScaledReciprocal.reciprocal (-a)⁻¹).toRingHom) := rfl
  rw [hρ] at H
  simpa only [Category.assoc, ProjectiveLine.overlapLeft] using H

/-- The complete first exceptional projective line in the actual coefficient equation gluing. -/
def coefficientShearAdjacentFirstComponent :
    ProjectiveLine.scheme S ⟶ coefficientShearGlued hπ data S r (j + 2 + m) hm :=
  ProjectiveLine.scaledReciprocalDesc a⁻¹ F₁ L₁
    (coefficientShearAdjacentFirstComponent_overlap
      hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha)

/-- The complete opposite projective line, including both original affine origins. -/
def coefficientShearAdjacentSecondComponent :
    ProjectiveLine.scheme S ⟶ coefficientShearGlued hπ data S r (j + 2 + m) hm :=
  ProjectiveLine.scaledReciprocalDesc (-a)⁻¹ F₂ L₂
    (coefficientShearAdjacentSecondComponent_overlap
      hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha)

local notation "C₁" => coefficientShearAdjacentFirstComponent
  hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha
local notation "C₂" => coefficientShearAdjacentSecondComponent
  hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha

/-- The first component keeps the entire first affine conic parameter. -/
@[reassoc] theorem coefficientShearAdjacentFirstComponent_left :
    ProjectiveLine.left S ≫ C₁ = F₁ := ProjectiveLine.scaledReciprocalDesc_left _ _ _ _

/-- Its other full affine chart retains the first reciprocal tangent scale. -/
@[reassoc] theorem coefficientShearAdjacentFirstComponent_right :
    ProjectiveLine.right S ≫ C₁ = ProjectiveLine.chartScaling S a⁻¹ ≫ L₁ :=
  ProjectiveLine.scaledReciprocalDesc_right _ _ _ _

/-- The second component keeps the entire opposite conic parameter. -/
@[reassoc] theorem coefficientShearAdjacentSecondComponent_left :
    ProjectiveLine.left S ≫ C₂ = F₂ := ProjectiveLine.scaledReciprocalDesc_left _ _ _ _

/-- Its other chart retains the negative reciprocal scale on the original second line. -/
@[reassoc] theorem coefficientShearAdjacentSecondComponent_right :
    ProjectiveLine.right S ≫ C₂ = ProjectiveLine.chartScaling S (-a)⁻¹ ≫ L₂ :=
  ProjectiveLine.scaledReciprocalDesc_right _ _ _ _

/-- The first infinity is the actual next retained first-line origin. -/
@[reassoc] theorem coefficientShearAdjacentFirstComponent_infinity :
    ProjectiveLine.infinity S ≫ C₁ = ProjectiveLine.chartZero S ≫ L₁ :=
  ProjectiveLine.scaledReciprocalDesc_infinity _ _ _ _

/-- The second infinity is the actual next retained opposite-line origin. -/
@[reassoc] theorem coefficientShearAdjacentSecondComponent_infinity :
    ProjectiveLine.infinity S ≫ C₂ = ProjectiveLine.chartZero S ≫ L₂ :=
  ProjectiveLine.scaledReciprocalDesc_infinity _ _ _ _

end FLT.Mazur.WeierstrassDividedDepth
