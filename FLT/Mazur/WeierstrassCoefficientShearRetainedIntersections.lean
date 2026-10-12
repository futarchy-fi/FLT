/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
public import FLT.Mazur.WeierstrassSuccessiveShearConicBoundary
public import FLT.Mazur.WeierstrassSuccessiveShearLineOpen

/-!
# Full retained component intersections inside the complete equation gluing

Embed each original tensor chart in the actual glued model. Its conic
incidence boundary and punctured tangent lines retain their cartesian
squares there, with the complete original component maps as projections.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (t : ℕ) (ht : t ≤ n) (i : Fin t)
local notation "d" => data (Fin.mk (i.val + 1) (by omega))
local notation "s₀" => π ^ (start + i.val)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "a" => WeierstrassCurve.a₁ U
local notation "c" => algebraMap R S (Data.b6 d)
local notation "ci" => successiveCoefficientShearIso W s₀ π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r
local notation "T₀" => ScalarExtension W s₀ π (Data.b3 d) (Data.b4 d) (Data.b6 d) S

/-- Each original complete tensor equation embedded in the actual sheared gluing. -/
def coefficientShearRetainedTensorChart :
    Spec (.of T₀) ⟶ coefficientShearGlued hπ data S r t ht :=
  (ci).inv ≫ coefficientShearGluedChart hπ data S r t ht (.inr i)

instance coefficientShearRetainedTensorChart_isOpenImmersion :
    IsOpenImmersion (coefficientShearRetainedTensorChart hπ data S r t ht i) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

local notation "j" => coefficientShearRetainedTensorChart hπ data S r t ht i
variable (hs : algebraMap R S (π ^ (start + i.val)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨i.val + 1, by omega⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨i.val + 1, by omega⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "f" => tensorShearMiddleEquiv W s₀ π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4
local notation "nf" => coefficientShearMiddleEquiv W s₀ π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4

/-- The original tensor normal form occupies exactly its constructed retained equation. -/
theorem coefficientShearRetainedTensorChart_middle :
    (Scheme.Spec.mapIso (f).toRingEquiv.toCommRingCatIso.op).hom ≫ j =
      coefficientShearRetainedFiber hπ data S r t ht i hs hp h3 h4 := by
  have he : (Scheme.Spec.mapIso (f).toRingEquiv.toCommRingCatIso.op).hom =
      (Scheme.Spec.mapIso (nf).toRingEquiv.toCommRingCatIso.op).hom ≫ (ci).hom := by
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  rw [he, coefficientShearRetainedTensorChart, coefficientShearRetainedFiber]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

local notation "conic" => tensorShearConicImmersion W s₀ π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr
local notation "ti" => PrincipalOpenTensor.inclusion S
  (coord W s₀ π (Data.b3 d) (Data.b4 d) (Data.b6 d) 0)
local notation "ui" => PrincipalOpenTensor.inclusion S
  (coord W s₀ π (Data.b3 d) (Data.b4 d) (Data.b6 d) 2)

/-- The whole original tensor conic is precisely the retained conic in the glued model. -/
theorem coefficientShearRetainedTensorChart_conic : conic ≫ j =
    coefficientShearRetainedConic hπ data S r t ht i hs hp h3 h4 hr := by
  rw [tensorShearConicImmersion, Category.assoc, coefficientShearRetainedTensorChart_middle]
  rfl

set_option maxHeartbeats 600000 in
-- Elaborating the two indexed localization presentations exceeds the default limit.
/-- The complete incidence-open intersection remains cartesian in the actual equation gluing. -/
theorem coefficientShearRetainedConic_boundary_isPullback :
    IsPullback
      (tensorShearConicBoundaryIso W s₀ π (Data.b3 d) (Data.b4 d) (Data.b6 d)
        S r hs hp h3 h4 hr).hom
      (PrincipalOpenTransport.inclusion (conicT a c)) (ti ≫ j)
      (coefficientShearRetainedConic hπ data S r t ht i hs hp h3 h4 hr) := by
  rw [← coefficientShearRetainedTensorChart_conic]
  have sq := tensorShearConicBoundary_isPullback W s₀ π
    (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _ j sq.cone sq.isLimit)

variable (v : S) (hv : v * (v + (rootShearCurve (W.map (algebraMap R S)) r).a₁) = 0)
local notation "line" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (tensorShearLineMap W s₀ π (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr v hv)))
local notation "p" => Spec.map (CommRingCat.ofHom
  (Polynomial.toLaurent : Polynomial S →+* S[T;T⁻¹]))

/-- Both entire tangent lines retain their actual coefficient-model embeddings. -/
theorem coefficientShearRetainedTensorChart_line : line ≫ j =
    coefficientShearRetainedLine hπ data S r t ht i hs hp h3 h4 hr v hv := by
  have he : line = middleLineImmersion U c (coefficientShear_a₂_zero W S r hr) v hv ≫
      (Scheme.Spec.mapIso (f).toRingEquiv.toCommRingCatIso.op).hom := by
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  rw [he, Category.assoc, coefficientShearRetainedTensorChart_middle]
  rfl

/-- The full horizontal intersection of each retained line in the complete glued model. -/
theorem coefficientShearRetainedLine_boundary_isPullback :
    IsPullback
      (tensorShearLineToHorizontal W s₀ π (Data.b3 d) (Data.b4 d) (Data.b6 d)
        S r hs hp h3 h4 hr v hv) p (ui ≫ j)
      (coefficientShearRetainedLine hπ data S r t ht i hs hp h3 h4 hr v hv) := by
  rw [← coefficientShearRetainedTensorChart_line]
  have sq := tensorShearLineHorizontal_isPullback W s₀ π
    (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr v hv
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _ j sq.cone sq.isLimit)

end FLT.Mazur.WeierstrassDividedDepth
