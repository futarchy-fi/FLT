/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
public import FLT.Mazur.WeierstrassSuccessiveXMiddleMarkedDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Descent to every actual retained coefficient equation

Transport the full marked conic-and-lines descent through the retained
coefficient normal form, including its original divided constant.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S)
  (t : ℕ) (ht : t ≤ n) (i : Fin t)
local notation "d" => data (Fin.mk (i.val + 1) (by omega))
local notation "q" => algebraMap R S
local notation "U" => rootShearCurve (W.map q) r
local notation "a" => WeierstrassCurve.a₁ U
local notation "c" => q (Data.b6 d)
variable (hs : algebraMap R S (π ^ (start + i.val)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨i.val + 1, by omega⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨i.val + 1, by omega⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "e" => coefficientShearMiddleEquiv W (π ^ (start + i.val)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4
local notation "h2" => coefficientShear_a₂_zero W S r hr

/-- The full normal middle equation identifies the actual retained atlas object. -/
def coefficientShearRetainedEquationIso :
    Spec (.of (WeierstrassSuccessiveX.Coordinate U 0 0 0 0 c)) ≅
      coefficientShearAtlasObject data S r t ht (.inr i) :=
  Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op
local notation "E" => coefficientShearRetainedEquationIso data S r t ht i hs hp h3 h4

/-- The normal comparison recovers the original retained chart in the complete gluing. -/
theorem coefficientShearRetainedEquationIso_chart [IsDomain R] [IsBezout R]
    (hπ : π ≠ 0) :
    (E).hom ≫ coefficientShearGluedChart hπ data S r t ht (.inr i) =
      coefficientShearRetainedFiber hπ data S r t ht i hs hp h3 h4 := rfl

variable (ha : IsUnit (rootShearCurve (W.map (algebraMap R S)) r).a₁)
  {Y : Scheme.{u}}
  (f : Spec (.of (ConicCoordinate
    (rootShearCurve (W.map (algebraMap R S)) r).a₁
    (algebraMap R S (data ⟨i.val + 1, by omega⟩).b6))) ⟶ Y)
  (g₁ g₂ : ProjectiveLine.chart S ⟶ Y)
  (w₁ : Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint
    (rootShearCurve (W.map (algebraMap R S)) r).a₁
    (algebraMap R S (data ⟨i.val + 1, by omega⟩).b6) ha).toRingHom) ≫ f =
      ProjectiveLine.chartZero S ≫ g₁)
  (w₂ : Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint
    (rootShearCurve (W.map (algebraMap R S)) r).a₁
    (algebraMap R S (data ⟨i.val + 1, by omega⟩).b6) ha).toRingHom) ≫ f =
      ProjectiveLine.chartZero S ≫ g₂)

/-- The complete actual retained equation receives its compatible original component maps. -/
@[irreducible] def coefficientShearRetainedEquationDesc :
    coefficientShearAtlasObject data S r t ht (.inr i) ⟶ Y :=
  (E).inv ≫ middleMarkedDesc U c h2 ha f g₁ g₂ w₁ w₂

/-- The actual coefficient comparison recovers the full middle-fiber descent. -/
theorem coefficientShearRetainedEquationDesc_normal :
    (E).hom ≫ coefficientShearRetainedEquationDesc
      data S r t ht i hs hp h3 h4 hr ha f g₁ g₂ w₁ w₂ =
        middleMarkedDesc U c h2 ha f g₁ g₂ w₁ w₂ := by
  rw [coefficientShearRetainedEquationDesc, Iso.hom_inv_id_assoc]

/-- The actual retained conic recovers its entire prescribed morphism. -/
theorem coefficientShearRetainedEquationDesc_conic :
    middleConicImmersion U c h2 ≫ (E).hom ≫ coefficientShearRetainedEquationDesc
      data S r t ht i hs hp h3 h4 hr ha f g₁ g₂ w₁ w₂ = f := by
  rw [coefficientShearRetainedEquationDesc_normal, middleMarkedDesc_conic]

/-- The actual first retained line recovers its prescribed morphism. -/
theorem coefficientShearRetainedEquationDesc_first :
    middleLineImmersion U c h2 0 (middle_first_root U) ≫ (E).hom ≫
      coefficientShearRetainedEquationDesc data S r t ht i hs hp h3 h4 hr ha f g₁ g₂ w₁ w₂ =
        g₁ := by
  rw [coefficientShearRetainedEquationDesc_normal, middleMarkedDesc_first]

/-- The actual opposite retained line recovers its prescribed morphism. -/
theorem coefficientShearRetainedEquationDesc_second :
    middleLineImmersion U c h2 (-a) (middle_second_root U) ≫ (E).hom ≫
      coefficientShearRetainedEquationDesc data S r t ht i hs hp h3 h4 hr ha f g₁ g₂ w₁ w₂ =
        g₂ := by
  rw [coefficientShearRetainedEquationDesc_normal, middleMarkedDesc_second]

/-- The full original conic and both lines characterize the actual retained equation map. -/
theorem coefficientShearRetainedEquationDesc_unique
    (m : coefficientShearAtlasObject data S r t ht (.inr i) ⟶ Y)
    (hf : middleConicImmersion U c h2 ≫ (E).hom ≫ m = f)
    (h₁ : middleLineImmersion U c h2 0 (middle_first_root U) ≫ (E).hom ≫ m = g₁)
    (h₂ : middleLineImmersion U c h2 (-a) (middle_second_root U) ≫ (E).hom ≫ m = g₂) :
    m = coefficientShearRetainedEquationDesc
      data S r t ht i hs hp h3 h4 hr ha f g₁ g₂ w₁ w₂ := by
  apply (cancel_epi (E).hom).mp
  rw [coefficientShearRetainedEquationDesc_normal]
  apply middleFiber_components_hom_ext U c h2 ha
  · rw [hf, middleMarkedDesc_conic]
  · rw [h₁, middleMarkedDesc_first]
  · rw [h₂, middleMarkedDesc_second]

end FLT.Mazur.WeierstrassDividedDepth
