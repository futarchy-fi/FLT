/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearScaleOneComponents
public import FLT.Mazur.WeierstrassCoefficientShearStageIso
import all FLT.Mazur.WeierstrassCoefficientShearScaleOneComponents
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Original conic origins of both complete scale-one components

The complete affine parameter identifies the zero endpoint with its actual
conic incidence section. No original conic constant is replaced.
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
variable (hs : algebraMap R S (π ^ (start + j)) = 1) (hp : algebraMap R S π = 0)
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
local notation "conic" => tensorShearScaleOneConicImmersion W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp g3 g4 hr ≫
    coefficientShearRetainedTensorChart hπ data S r (j + 2 + m) hm (Fin.mk j (by omega))
local notation "inc" => PrincipalOpenTransport.inclusion
  (conicT (WeierstrassCurve.a₁ U) c)
local notation "line" => coefficientShearRetainedLine hπ data S r (j + 2 + m) hm
  (Fin.mk (j + 1) (by omega)) hsNext hp h3 h4 hr

local notation "E" => conicZeroAffineIso c gc
local notation "F₁" => (E).hom ≫ coefficientConicFirstParameter (U).a₁ c hu conic
local notation "F₂" => (E).hom ≫ coefficientConicSecondParameter (U).a₁ c hu conic
local notation "L₁" => line 0 (middle_first_root U)
local notation "L₂" => line (-(U).a₁) (middle_second_root U)

local notation "C₁" => coefficientShearScaleOneFirstComponent
  hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha
local notation "C₂" => coefficientShearScaleOneSecondComponent
  hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha

/-- Zero of the first full scale-one component is its original conic marking. -/
@[reassoc] theorem coefficientShearScaleOneFirstComponent_zero :
    ProjectiveLine.zero S ≫ C₁ =
      Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint (U).a₁ c hu).toRingHom) ≫
        conic := by
  rw [ProjectiveLine.zero, Category.assoc, coefficientShearScaleOneFirstComponent_left,
    ← Category.assoc, conicZeroAffineIso_origin, coefficientConicFirstParameter,
    conicFirstParameterIso_origin_assoc]

/-- Zero of the opposite full scale-one component is the opposite original conic marking. -/
@[reassoc] theorem coefficientShearScaleOneSecondComponent_zero :
    ProjectiveLine.zero S ≫ C₂ =
      Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint (U).a₁ c hu).toRingHom) ≫
        conic := by
  rw [ProjectiveLine.zero, Category.assoc, coefficientShearScaleOneSecondComponent_left,
    ← Category.assoc, conicZeroAffineIso_origin, coefficientConicSecondParameter,
    conicSecondParameterIso_origin_assoc]

omit hj hjNext h3 h4 in
/-- A change of stage expression preserves the complete retained tensor chart. -/
@[reassoc] theorem coefficientShearRetainedTensorChart_stageIso
    (t : ℕ) (ht : t ≤ n) (i : Fin t) (k : ℕ) (hk : k ≤ n) (hstage : t = k) :
    coefficientShearRetainedTensorChart hπ data S r t ht i ≫
        (coefficientShearStageIso hπ data S r t k ht hk hstage).hom =
      coefficientShearRetainedTensorChart hπ data S r k hk ⟨i.val, by omega⟩ := by
  subst k
  exact Category.comp_id _

end FLT.Mazur.WeierstrassDividedDepth
