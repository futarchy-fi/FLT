/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedLineProjection
import all FLT.Mazur.WeierstrassCoefficientShearRetainedLineProjection
public import FLT.Mazur.WeierstrassSuccessiveShearScaleOneIncidence
public import FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic
public import FLT.Mazur.WeierstrassDividedTerminalParameterStructure
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections

/-!
# The complete scale-one incidence line in the actual retained target

The full original polynomial parameter embeds at every later stage. Both
markings are the original conic attachments, for arbitrary terminal constant.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
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
  (j : ℕ) (hj : j + 1 ≤ n) (m : ℕ) (hm : j + 1 + m ≤ n)
  (hs : algebraMap R S (π ^ (start + j)) = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, by omega⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, by omega⟩).b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => (rootShearCurve (W.map (algebraMap R S)) r).a₁
local notation "c₀" => algebraMap R S (Data.b6 d)
local notation "T₀" => ScalarExtension W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S
local notation "B" => coefficientShearRetainedTensorChart hπ data S r
  (j + 1 + m) hm ⟨j, by omega⟩
local notation "C" => tensorShearScaleOneConicImmersion W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr
local notation "P" => coefficientShearGluedProjection hπ data S r (j + 1 + m) hm
local notation "c" => originalShearScaleOneConicMap W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr
local notation "F" => olderSuccessiveChart hπ data j hj m hm ≫
  finiteLocalChart hπ data (j + 1 + m) hm

local notation "L" => tensorShearScaleOneIncidenceMap W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr

/-- The whole original incidence line inside its retained scale-one tensor chart. -/
def coefficientShearRetainedScaleOneIncidence :
    ProjectiveLine.chart S ⟶ coefficientShearGlued hπ data S r (j + 1 + m) hm :=
  Spec.map (CommRingCat.ofHom (L).toRingHom) ≫ B
local notation "I" => coefficientShearRetainedScaleOneIncidence
  hπ data S r j hj m hm hs hp h3 h4 hr
local notation "K" => coefficientShearRetainedScaleOneConic
  hπ data S r j hj m hm hs hp h3 h4 hr

/-- The entire line retains its coefficient structure. -/
@[reassoc] theorem coefficientShearRetainedScaleOneIncidence_structure :
    I ≫ coefficientShearGluedStructure hπ data S r (j + 1 + m) hm =
      ProjectiveLine.chartToBase S := by
  rw [coefficientShearRetainedScaleOneIncidence, Category.assoc,
    coefficientShearRetainedScaleOneTensor_structure hπ data S r j hj m hm]
  exact terminalComponent_algebra_structure L

/-- The entire line projects through its actual integral chart functions. -/
@[reassoc] theorem coefficientShearRetainedScaleOneIncidence_projection :
    I ≫ P = Spec.map (CommRingCat.ofHom
      (originalShearScaleOneIncidenceMap W (π ^ (start + j)) π
        (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr).toRingHom) ≫ F := by
  rw [coefficientShearRetainedScaleOneIncidence, Category.assoc,
    coefficientShearRetainedTensorChart_projection hπ data S r j hj m hm,
    ← Category.assoc]
  apply congrArg (· ≫ F)
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

variable (ha : IsUnit (rootShearCurve (W.map (algebraMap R S)) r).a₁)

/-- Zero of the full slope line is the original first conic incidence point. -/
@[reassoc] theorem coefficientShearRetainedScaleOneIncidence_first :
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (0 : S)).toRingHom) ≫ I =
      Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint a c₀ ha).toRingHom) ≫ K := by
  rw [coefficientShearRetainedScaleOneIncidence, coefficientShearRetainedScaleOneConic,
    tensorShearScaleOneConicImmersion_eq_spec, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (tensorShearScaleOneIncidenceMap_first W (π ^ (start + j)) π
      (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr ha)

/-- The opposite full slope marking is the original second conic incidence point. -/
@[reassoc] theorem coefficientShearRetainedScaleOneIncidence_second :
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (-a)).toRingHom) ≫ I =
      Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint a c₀ ha).toRingHom) ≫ K := by
  rw [coefficientShearRetainedScaleOneIncidence, coefficientShearRetainedScaleOneConic,
    tensorShearScaleOneConicImmersion_eq_spec, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (tensorShearScaleOneIncidenceMap_second W (π ^ (start + j)) π
      (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr ha)

end FLT.Mazur.WeierstrassDividedDepth
