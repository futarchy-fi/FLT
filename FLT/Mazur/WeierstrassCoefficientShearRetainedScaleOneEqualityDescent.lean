/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneDescent
public import FLT.Mazur.WeierstrassCoefficientShearScaleOneEqualityParameters
public import FLT.Mazur.ProjectiveLineSlopeNormalization

/-!
# Two full projective inputs on the scale-one equality chart

The actual completed nonzero-constant conic and exterior descend together.
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
  (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "s₀" => π ^ (start + j)
local notation "a" => (rootShearCurve (W.map (algebraMap R S)) r).a₁
local notation "c" => algebraMap R S (Data.b6 d)
local notation "T" => ScalarExtension W s₀ π (Data.b3 d) (Data.b4 d) (Data.b6 d) S

local notation "E" => coefficientShearRetainedScaleOneTensorIso
  data S r (j + 1) hj ⟨j, Nat.lt_succ_self j⟩

variable (hs : algebraMap R S (π ^ (start + j)) = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "C" => tensorShearScaleOneConicImmersion W s₀ π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr
local notation "L" => Spec.map (CommRingCat.ofHom (tensorShearScaleOneIncidenceMap W s₀ π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr).toRingHom)
variable (a₀ : Sˣ) (ha₀ : (a₀ : S) =
    (rootShearCurve (W.map (algebraMap R S)) r).a₁)
  (hc : IsUnit (algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6))
local notation "hu" => Eq.mp (congrArg IsUnit ha₀) (Units.isUnit a₀)
local notation "q" => coefficientShearScaleOneEqualityConicParameter
  data S r j hj hp h3 h4 hc hr a₀ ha₀
variable {Y : Scheme.{u}} (f g : ProjectiveLine.scheme S ⟶ Y)
  (w₁ : ProjectiveLine.zero S ≫ f = ProjectiveLine.zero S ≫ g)
  (w₂ : ProjectiveLine.infinity S ≫ f = ProjectiveLine.infinity S ≫ g)
local notation "N" => ProjectiveLine.left S ≫ (ProjectiveLine.slopeNormalizationIso a₀).hom

/-- The completed original conic and exterior descend to the entire equality equation. -/
@[irreducible] def coefficientShearRetainedScaleOneEqualityDesc :
    coefficientShearAtlasObject data S r (j + 1) hj (.inr ⟨j, Nat.lt_succ_self j⟩) ⟶ Y :=
  coefficientShearRetainedScaleOneDesc data S r (j + 1) hj ⟨j, Nat.lt_succ_self j⟩
    hs hp h3 h4 hr hu (q ≫ f) (N ≫ g)
    (by
      rw [coefficientShearScaleOneEqualityConicParameter_first_assoc]
      simp only [Category.assoc]
      rw [← Category.assoc (ProjectiveLine.chartZero S) (ProjectiveLine.left S)]
      change _ = ProjectiveLine.infinitySlopeMark (0 : S) ≫
        (ProjectiveLine.slopeNormalizationIso a₀).hom ≫ g
      rw [ProjectiveLine.slopeNormalization_first_assoc]
      exact w₁)
    (by
      rw [coefficientShearScaleOneEqualityConicParameter_second_assoc]
      simp only [Category.assoc]
      rw [← Category.assoc _ (ProjectiveLine.left S)]
      change _ = ProjectiveLine.infinitySlopeMark (-a) ≫
        (ProjectiveLine.slopeNormalizationIso a₀).hom ≫ g
      rw [← ha₀, ProjectiveLine.slopeNormalization_second_assoc]
      exact w₂)
local notation "D" => coefficientShearRetainedScaleOneEqualityDesc
  data S r j hj hs hp h3 h4 hr a₀ ha₀ hc f g w₁ w₂

/-- The entire original conic retains its map through the completed component. -/
@[reassoc] theorem coefficientShearRetainedScaleOneEqualityDesc_conic :
    C ≫ (E).inv ≫ D = q ≫ f := by
  rw [coefficientShearRetainedScaleOneEqualityDesc]
  exact coefficientShearRetainedScaleOneDesc_conic
    data S r (j + 1) hj ⟨j, Nat.lt_succ_self j⟩ hs hp h3 h4 hr hu _ _ _ _

/-- The complete incidence line retains the exterior's original slope parameter. -/
@[reassoc] theorem coefficientShearRetainedScaleOneEqualityDesc_exterior :
    L ≫ (E).inv ≫ D = N ≫ g := by
  rw [coefficientShearRetainedScaleOneEqualityDesc]
  exact coefficientShearRetainedScaleOneDesc_incidence
    data S r (j + 1) hj ⟨j, Nat.lt_succ_self j⟩ hs hp h3 h4 hr hu _ _ _ _

/-- The full conic and exterior restrictions characterize the actual equality-chart map. -/
theorem coefficientShearRetainedScaleOneEqualityDesc_unique
    (m : coefficientShearAtlasObject data S r (j + 1) hj
      (.inr ⟨j, Nat.lt_succ_self j⟩) ⟶ Y)
    (hf : C ≫ (E).inv ≫ m = q ≫ f) (hg : L ≫ (E).inv ≫ m = N ≫ g) : m = D := by
  rw [coefficientShearRetainedScaleOneEqualityDesc]
  exact coefficientShearRetainedScaleOneDesc_unique
    data S r (j + 1) hj ⟨j, Nat.lt_succ_self j⟩ hs hp h3 h4 hr hu _ _ _ _ m hf hg

end FLT.Mazur.WeierstrassDividedDepth
