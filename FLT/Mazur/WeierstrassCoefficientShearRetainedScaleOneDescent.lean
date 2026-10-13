/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearScaleOneDescent
public import FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneIncidence
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections

/-!
# Full scale-one descent on the actual retained coefficient equation

Transport both complete component inputs through the original coefficient shear.
The original conic constant and the entire incidence line are preserved.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
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
local notation "s₀" => π ^ (start + i.val)
local notation "a" => (rootShearCurve (W.map (algebraMap R S)) r).a₁
local notation "c" => algebraMap R S (Data.b6 d)
local notation "T" => ScalarExtension W s₀ π (Data.b3 d) (Data.b4 d) (Data.b6 d) S

/-- The actual retained coefficient equation identifies its entire original tensor chart. -/
def coefficientShearRetainedScaleOneTensorIso :
    coefficientShearAtlasObject data S r t ht (.inr i) ≅ Spec (.of T) :=
  successiveCoefficientShearIso W s₀ π (Data.b3 d) (Data.b4 d) (Data.b6 d) S r
local notation "E" => coefficientShearRetainedScaleOneTensorIso data S r t ht i

/-- The tensor comparison retains the original chart embedding in the global target. -/
@[reassoc] theorem coefficientShearRetainedScaleOneTensorIso_chart
    [IsDomain R] [IsBezout R] (hπ : π ≠ 0) :
    (E).inv ≫ coefficientShearGluedChart hπ data S r t ht (.inr i) =
      coefficientShearRetainedTensorChart hπ data S r t ht i := rfl

variable (hs : algebraMap R S (π ^ (start + i.val)) = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨i.val + 1, by omega⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨i.val + 1, by omega⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "C" => tensorShearScaleOneConicImmersion W s₀ π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr
local notation "L" => Spec.map (CommRingCat.ofHom (tensorShearScaleOneIncidenceMap W s₀ π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr).toRingHom)
variable (ha : IsUnit (rootShearCurve (W.map (algebraMap R S)) r).a₁)
  {Y : Scheme.{u}} (f : Spec (.of (ConicCoordinate
    (rootShearCurve (W.map (algebraMap R S)) r).a₁
    (algebraMap R S (Data.b6 (data ⟨i.val + 1, by omega⟩))))) ⟶ Y)
  (g : ProjectiveLine.chart S ⟶ Y)
  (w₁ : Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint
    (rootShearCurve (W.map (algebraMap R S)) r).a₁
    (algebraMap R S (Data.b6 (data ⟨i.val + 1, by omega⟩))) ha).toRingHom) ≫ f =
      ProjectiveLine.chartZero S ≫ g)
  (w₂ : Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint
    (rootShearCurve (W.map (algebraMap R S)) r).a₁
    (algebraMap R S (Data.b6 (data ⟨i.val + 1, by omega⟩))) ha).toRingHom) ≫ f =
      Spec.map (CommRingCat.ofHom (aeval
        (-(rootShearCurve (W.map (algebraMap R S)) r).a₁)).toRingHom) ≫ g)
local notation "D₀" => tensorShearScaleOneDesc W s₀ π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr ha f g w₁ w₂

/-- Full compatible conic and line maps descend to the actual retained atlas equation. -/
@[irreducible] def coefficientShearRetainedScaleOneDesc :
    coefficientShearAtlasObject data S r t ht (.inr i) ⟶ Y := (E).hom ≫ D₀
local notation "D" => coefficientShearRetainedScaleOneDesc
  data S r t ht i hs hp h3 h4 hr ha f g w₁ w₂

/-- The descent retains the full original tensor-chart map. -/
@[reassoc] theorem coefficientShearRetainedScaleOneDesc_tensor : (E).inv ≫ D = D₀ := by
  rw [coefficientShearRetainedScaleOneDesc, Iso.inv_hom_id_assoc]

/-- Restriction recovers the entire original conic input, for arbitrary constant. -/
@[reassoc] theorem coefficientShearRetainedScaleOneDesc_conic : C ≫ (E).inv ≫ D = f := by
  rw [coefficientShearRetainedScaleOneDesc_tensor, tensorShearScaleOneDesc_conic]

/-- Restriction recovers the full original incidence line input. -/
@[reassoc] theorem coefficientShearRetainedScaleOneDesc_incidence : L ≫ (E).inv ≫ D = g := by
  rw [coefficientShearRetainedScaleOneDesc_tensor, tensorShearScaleOneDesc_incidence]

/-- The two full component restrictions characterize the actual retained equation map. -/
theorem coefficientShearRetainedScaleOneDesc_unique
    (m : coefficientShearAtlasObject data S r t ht (.inr i) ⟶ Y)
    (hf : C ≫ (E).inv ≫ m = f) (hg : L ≫ (E).inv ≫ m = g) : m = D := by
  apply (cancel_epi (E).inv).mp
  rw [coefficientShearRetainedScaleOneDesc_tensor]
  exact tensorShearScaleOneDesc_unique W s₀ π
    (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr ha f g w₁ w₂ _ hf hg

end FLT.Mazur.WeierstrassDividedDepth
