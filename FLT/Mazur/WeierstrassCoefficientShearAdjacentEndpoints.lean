/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearAdjacentComponents
public import FLT.Mazur.WeierstrassCoefficientShearConicOrigins
public import FLT.Mazur.WeierstrassCoefficientShearRetainedAttachments
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentComponents

import all FLT.Mazur.WeierstrassCoefficientShearRetainedAttachments

/-!
# The actual adjacent component endpoints

The zero of each full adjacent component is the preceding retained line origin.
The conic attachment square proves the identification inside the actual model.
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

local notation "C₁" => coefficientShearAdjacentFirstComponent
  hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha
local notation "C₂" => coefficientShearAdjacentSecondComponent
  hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha
local notation "prev" => coefficientShearRetainedLine hπ data S r (j + 2 + m) hm
  (Fin.mk j (by omega)) hs hp g3 g4 hr

/-- The first zero is the preceding actual first-line origin. -/
@[reassoc] theorem coefficientShearAdjacentFirstComponent_zero :
    ProjectiveLine.zero S ≫ C₁ =
      ProjectiveLine.chartZero S ≫ prev 0 (middle_first_root U) := by
  rw [ProjectiveLine.zero, Category.assoc, coefficientShearAdjacentFirstComponent_left,
    coefficientConicFirstParameter_affine_origin]
  exact coefficientShearRetainedFirstAttachment
    hπ data S r (j + 2 + m) hm ⟨j, by omega⟩ hs hp g3 g4 hr hu

/-- The opposite zero is the preceding actual second-line origin. -/
@[reassoc] theorem coefficientShearAdjacentSecondComponent_zero :
    ProjectiveLine.zero S ≫ C₂ =
      ProjectiveLine.chartZero S ≫ prev (-(U).a₁) (middle_second_root U) := by
  rw [ProjectiveLine.zero, Category.assoc, coefficientShearAdjacentSecondComponent_left,
    coefficientConicSecondParameter_affine_origin]
  exact coefficientShearRetainedSecondAttachment
    hπ data S r (j + 2 + m) hm ⟨j, by omega⟩ hs hp g3 g4 hr hu

end FLT.Mazur.WeierstrassDividedDepth
