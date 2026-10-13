/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedEquationDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedEquationDescent

/-!
# Coefficient structure of full retained-equation descent

The complete conic and both lines determine the base structure of the descended map.
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

local notation "E" => coefficientShearRetainedEquationIso data S r t ht i hs hp h3 h4
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

local notation "D" => coefficientShearRetainedEquationDesc
  data S r t ht i hs hp h3 h4 hr ha f g₁ g₂ w₁ w₂
variable (p : Y ⟶ Spec (.of S))
  (hf : f ≫ p = conicStructure (rootShearCurve (W.map (algebraMap R S)) r).a₁
    (algebraMap R S (data ⟨i.val + 1, by omega⟩).b6))
  (hg₁ : g₁ ≫ p = ProjectiveLine.chartToBase S)
  (hg₂ : g₂ ≫ p = ProjectiveLine.chartToBase S)

include hf hg₁ hg₂ in
/-- Full retained descent preserves the base when each original component map does. -/
theorem coefficientShearRetainedEquationDesc_structure :
    D ≫ p = coefficientShearAtlasStructure data S r t ht (.inr i) := by
  have hbase : (E).hom ≫ coefficientShearAtlasStructure data S r t ht (.inr i) =
      Spec.map (CommRingCat.ofHom
        (algebraMap S (WeierstrassSuccessiveX.Coordinate U 0 0 0 0 c))) :=
    terminalComponent_algebra_structure (e).toAlgHom
  apply (cancel_epi (E).hom).mp
  rw [hbase]
  apply middleFiber_components_hom_ext U c h2 ha
  · have H := congrArg (fun m => m ≫ p)
      (coefficientShearRetainedEquationDesc_conic
        data S r t ht i hs hp h3 h4 hr ha f g₁ g₂ w₁ w₂)
    simp only [Category.assoc] at H ⊢
    rw [H, hf]
    exact (terminalComponent_algebra_structure (middleConicMap U c h2)).symm
  · have H := congrArg (fun m => m ≫ p)
      (coefficientShearRetainedEquationDesc_first
        data S r t ht i hs hp h3 h4 hr ha f g₁ g₂ w₁ w₂)
    simp only [Category.assoc] at H ⊢
    rw [H, hg₁]
    exact (terminalComponent_algebra_structure
      (middleLineMap U c h2 0 (middle_first_root U))).symm
  · have H := congrArg (fun m => m ≫ p)
      (coefficientShearRetainedEquationDesc_second
        data S r t ht i hs hp h3 h4 hr ha f g₁ g₂ w₁ w₂)
    simp only [Category.assoc] at H ⊢
    rw [H, hg₂]
    exact (terminalComponent_algebra_structure
      (middleLineMap U c h2 (-a) (middle_second_root U))).symm

/-- The full retained map is therefore an actual morphism over the coefficient field. -/
def coefficientShearRetainedEquationOverDesc :
    Over.mk (coefficientShearAtlasStructure data S r t ht (.inr i)) ⟶ Over.mk p :=
  Over.homMk D (coefficientShearRetainedEquationDesc_structure
    data S r t ht i hs hp h3 h4 hr ha f g₁ g₂ w₁ w₂ p hf hg₁ hg₂)

end FLT.Mazur.WeierstrassDividedDepth
