/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneZeroDescent
public import FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneHomExt
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneHomExt
public import FLT.Mazur.WeierstrassProjectiveFiberDescentStructure
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneZeroDescent

/-!
# The full scale-one zero descent preserves the coefficient field

The two original conic branches and the complete exterior determine the base equation.
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

variable (p : Y ⟶ Spec (.of S))
  (hf₁ : f₁ ≫ p = ProjectiveLine.toBase S) (hf₂ : f₂ ≫ p = ProjectiveLine.toBase S)
  (hg : g ≫ p = ProjectiveLine.toBase S)

include hf₁ hf₂ hg in
/-- All three original component inputs descend over their common coefficient field. -/
theorem coefficientShearRetainedScaleOneZeroDesc_structure :
    coefficientShearRetainedScaleOneZeroDesc
      data S r t ht i hs hp h3 h4 hr a₀ ha₀ hc f₁ f₂ g w₁ w₂ ≫ p =
        coefficientShearAtlasStructure data S r t ht (.inr i) := by
  rw [coefficientShearRetainedScaleOneZeroDesc]
  apply coefficientShearRetainedScaleOneDesc_structure
  · exact conicZeroProjectiveDesc_structure a c hu hc f₁ f₂ p hf₁ hf₂
  · simp only [Category.assoc]
    rw [hg, ProjectiveLine.slopeNormalizationIso_base, ProjectiveLine.left_toBase]

end FLT.Mazur.WeierstrassDividedDepth
