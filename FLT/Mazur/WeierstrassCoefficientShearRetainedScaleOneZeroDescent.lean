/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneDescent
public import FLT.Mazur.WeierstrassConicZeroProjectiveDescent
public import FLT.Mazur.ProjectiveLineSlopeNormalization

/-!
# Three full projective inputs on a zero-constant scale-one chart

Both original conic branches and the exterior supply the entire retained equation.
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

local notation "E" => coefficientShearRetainedScaleOneTensorIso data S r t ht i

variable (hs : algebraMap R S (π ^ (start + i.val)) = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨i.val + 1, by omega⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨i.val + 1, by omega⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "C" => tensorShearScaleOneConicImmersion W s₀ π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr
local notation "L" => Spec.map (CommRingCat.ofHom (tensorShearScaleOneIncidenceMap W s₀ π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr).toRingHom)
variable (a₀ : Sˣ) (ha₀ : (a₀ : S) =
    (rootShearCurve (W.map (algebraMap R S)) r).a₁)
  (hc : algebraMap R S (data ⟨i.val + 1, by omega⟩).b6 = 0)
local notation "hu" => Eq.mp (congrArg IsUnit ha₀) (Units.isUnit a₀)
local notation "Z" => conicZeroAffineIso c hc
local notation "p₁" => (conicFirstParameterIso a c hu).inv ≫ conicFirstOpenImmersion a c
local notation "p₂" => (conicSecondParameterIso a c hu).inv ≫ conicSecondOpenImmersion a c
variable {Y : Scheme.{u}} (f₁ f₂ g : ProjectiveLine.scheme S ⟶ Y)
  (w₁ : ProjectiveLine.zero S ≫ f₁ = ProjectiveLine.zero S ≫ g)
  (w₂ : ProjectiveLine.zero S ≫ f₂ = ProjectiveLine.infinity S ≫ g)
local notation "N" => ProjectiveLine.left S ≫ (ProjectiveLine.slopeNormalizationIso a₀).hom
local notation "F" => conicZeroProjectiveDesc a c hu hc f₁ f₂

/-- The original three projective component inputs descend on the full scale-one equation. -/
@[irreducible] def coefficientShearRetainedScaleOneZeroDesc :
    coefficientShearAtlasObject data S r t ht (.inr i) ⟶ Y :=
  coefficientShearRetainedScaleOneDesc data S r t ht i hs hp h3 h4 hr hu F (N ≫ g)
    (by
      rw [conicZeroProjectiveDesc_first_origin]
      simp only [Category.assoc]
      rw [← Category.assoc (ProjectiveLine.chartZero S) (ProjectiveLine.left S)]
      change _ = ProjectiveLine.infinitySlopeMark (0 : S) ≫
        (ProjectiveLine.slopeNormalizationIso a₀).hom ≫ g
      rw [ProjectiveLine.slopeNormalization_first_assoc]
      exact w₁)
    (by
      rw [conicZeroProjectiveDesc_second_origin]
      simp only [Category.assoc]
      rw [← Category.assoc _ (ProjectiveLine.left S)]
      change _ = ProjectiveLine.infinitySlopeMark (-a) ≫
        (ProjectiveLine.slopeNormalizationIso a₀).hom ≫ g
      rw [← ha₀, ProjectiveLine.slopeNormalization_second_assoc]
      exact w₂)
local notation "D" => coefficientShearRetainedScaleOneZeroDesc
  data S r t ht i hs hp h3 h4 hr a₀ ha₀ hc f₁ f₂ g w₁ w₂

/-- The entire first conic branch retains its full original affine parameter. -/
theorem coefficientShearRetainedScaleOneZeroDesc_first :
    (Z).hom ≫ p₁ ≫ C ≫ (E).inv ≫ D = ProjectiveLine.left S ≫ f₁ := by
  rw [coefficientShearRetainedScaleOneZeroDesc,
    coefficientShearRetainedScaleOneDesc_conic, conicZeroProjectiveDesc_first]

/-- The entire opposite conic branch retains its independent full affine parameter. -/
theorem coefficientShearRetainedScaleOneZeroDesc_second :
    (Z).hom ≫ p₂ ≫ C ≫ (E).inv ≫ D = ProjectiveLine.left S ≫ f₂ := by
  rw [coefficientShearRetainedScaleOneZeroDesc,
    coefficientShearRetainedScaleOneDesc_conic, conicZeroProjectiveDesc_second]

/-- The whole incidence line receives the actual slope-normalized exterior input. -/
theorem coefficientShearRetainedScaleOneZeroDesc_exterior :
    L ≫ (E).inv ≫ D = N ≫ g := by
  rw [coefficientShearRetainedScaleOneZeroDesc, coefficientShearRetainedScaleOneDesc_incidence]

/-- These three entire component restrictions determine the actual equation map. -/
theorem coefficientShearRetainedScaleOneZeroDesc_unique
    (m : coefficientShearAtlasObject data S r t ht (.inr i) ⟶ Y)
    (hf₁ : (Z).hom ≫ p₁ ≫ C ≫ (E).inv ≫ m = ProjectiveLine.left S ≫ f₁)
    (hf₂ : (Z).hom ≫ p₂ ≫ C ≫ (E).inv ≫ m = ProjectiveLine.left S ≫ f₂)
    (hg : L ≫ (E).inv ≫ m = N ≫ g) : m = D := by
  rw [coefficientShearRetainedScaleOneZeroDesc]
  apply coefficientShearRetainedScaleOneDesc_unique
  · exact conicZeroProjectiveDesc_unique a c hu hc f₁ f₂ _ hf₁ hf₂
  · exact hg

end FLT.Mazur.WeierstrassDividedDepth
