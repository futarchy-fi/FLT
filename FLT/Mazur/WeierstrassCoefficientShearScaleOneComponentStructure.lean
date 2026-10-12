/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearScaleOneComponents
import all FLT.Mazur.WeierstrassCoefficientShearScaleOneComponents
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentGluedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentGluedFullConic

/-!
# Coefficient structures of the complete scale-one projective components

Both projective gluings preserve the actual coefficient-field projection.
The verification uses every function of the full affine conic parameters.
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

local notation "g" => coefficientShearGluedStructure hπ data S r (j + 2 + m) hm
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap S (ConicParameterOpen c)))
local notation "C₁" => coefficientShearScaleOneFirstComponent
  hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha
local notation "C₂" => coefficientShearScaleOneSecondComponent
  hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha

omit h3 h4 in
/-- The original entire scale-one conic keeps its coefficient-field projection. -/
theorem coefficientShearScaleOneAdjacentConic_structure : conic ≫ g = conicStructure (U).a₁ c := by
  have hB : coefficientShearRetainedTensorChart hπ data S r (j + 2 + m) hm
      (Fin.mk j (by omega)) ≫ g = Spec.map (CommRingCat.ofHom
        (algebraMap S (ScalarExtension W (π ^ (start + j)) π
          (Data.b3 d) (Data.b4 d) (Data.b6 d) S))) := by
    rw [coefficientShearRetainedTensorChart, Category.assoc, coefficientShearGluedChart_structure]
    change (successiveCoefficientShearIso _ _ _ _ _ _ _ _).inv ≫
      Spec.map (CommRingCat.ofHom (algebraMap S _)) = _
    rw [← successiveCoefficientShearIso_structure, Iso.inv_hom_id_assoc]
  rw [Category.assoc, hB, tensorShearScaleOneConicImmersion_eq_spec]
  exact terminalComponent_algebra_structure _

omit h3 h4 in
/-- The entire first conic parameter has its original coefficient structure. -/
@[reassoc] theorem coefficientShearScaleOneFirstParameter_structure :
    coefficientConicFirstParameter (U).a₁ c hu conic ≫ g = b := by
  rw [coefficientConicFirstParameter, Category.assoc, Category.assoc,
    coefficientShearScaleOneAdjacentConic_structure hπ data S r j hj hjNext m hm hs hp hr]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  erw [terminalComponent_algebra_structure
    (Algebra.algHom S (ConicCoordinate (U).a₁ c) (ConicFirstOpen (U).a₁ c))]
  exact terminalComponent_algebra_structure
    (conicFirstParameterEquiv (U).a₁ c hu).symm.toAlgHom

omit h3 h4 in
/-- The entire opposite conic parameter preserves the same coefficient field. -/
@[reassoc] theorem coefficientShearScaleOneSecondParameter_structure :
    coefficientConicSecondParameter (U).a₁ c hu conic ≫ g = b := by
  rw [coefficientConicSecondParameter, Category.assoc, Category.assoc,
    coefficientShearScaleOneAdjacentConic_structure hπ data S r j hj hjNext m hm hs hp hr]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  erw [terminalComponent_algebra_structure
    (Algebra.algHom S (ConicCoordinate (U).a₁ c) (ConicSecondOpen (U).a₁ c))]
  exact terminalComponent_algebra_structure
    (conicSecondParameterEquiv (U).a₁ c hu).symm.toAlgHom

/-- The full first projective component is a morphism over the actual coefficient field. -/
@[reassoc] theorem coefficientShearScaleOneFirstComponent_structure :
    C₁ ≫ g = ProjectiveLine.toBase S := by
  apply pushout.hom_ext
  · change ProjectiveLine.left S ≫ C₁ ≫ g = ProjectiveLine.left S ≫ ProjectiveLine.toBase S
    rw [coefficientShearScaleOneFirstComponent_left_assoc,
      coefficientShearScaleOneFirstParameter_structure
        hπ data S r j hj hjNext m hm hs hp hr a ha, conicZeroAffineIso_structure,
      ProjectiveLine.left_toBase]
  · change ProjectiveLine.right S ≫ C₁ ≫ g = ProjectiveLine.right S ≫ ProjectiveLine.toBase S
    rw [coefficientShearScaleOneFirstComponent_right_assoc,
      coefficientShearRetainedLine_structure, ProjectiveLine.right_toBase]
    change ProjectiveLine.chartScaling S a⁻¹ ≫ ProjectiveLine.chartToBase S =
      ProjectiveLine.chartToBase S
    exact ProjectiveLine.chartScaling_toBase S a⁻¹

/-- The opposite full projective component retains the same field projection at both origins. -/
@[reassoc] theorem coefficientShearScaleOneSecondComponent_structure :
    C₂ ≫ g = ProjectiveLine.toBase S := by
  apply pushout.hom_ext
  · change ProjectiveLine.left S ≫ C₂ ≫ g = ProjectiveLine.left S ≫ ProjectiveLine.toBase S
    rw [coefficientShearScaleOneSecondComponent_left_assoc,
      coefficientShearScaleOneSecondParameter_structure
        hπ data S r j hj hjNext m hm hs hp hr a ha, conicZeroAffineIso_structure,
      ProjectiveLine.left_toBase]
  · change ProjectiveLine.right S ≫ C₂ ≫ g = ProjectiveLine.right S ≫ ProjectiveLine.toBase S
    rw [coefficientShearScaleOneSecondComponent_right_assoc,
      coefficientShearRetainedLine_structure, ProjectiveLine.right_toBase]
    change ProjectiveLine.chartScaling S (-a)⁻¹ ≫ ProjectiveLine.chartToBase S =
      ProjectiveLine.chartToBase S
    exact ProjectiveLine.chartScaling_toBase S (-a)⁻¹

end FLT.Mazur.WeierstrassDividedDepth
