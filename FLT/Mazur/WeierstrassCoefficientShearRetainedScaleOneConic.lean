/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedLineProjection
import all FLT.Mazur.WeierstrassCoefficientShearRetainedLineProjection
public import FLT.Mazur.WeierstrassSuccessiveShearScaleOneConicCoefficient
public import FLT.Mazur.WeierstrassDividedTerminalParameterStructure
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections

/-!
# The complete scale-one conic in the original model

The complete conic retains its actual integral chart embedding and all its
original functions, before composing with any cubic contraction.
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
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
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

/-- The entire scale-one conic inside the actual original retained tensor chart. -/
def coefficientShearRetainedScaleOneConic :
    Spec (.of (ConicCoordinate a c₀)) ⟶ coefficientShearGlued hπ data S r (j + 1 + m) hm :=
  C ≫ B

/-- The full tensor chart keeps its coefficient structure before restricting to a component. -/
theorem coefficientShearRetainedScaleOneTensor_structure :
    B ≫ coefficientShearGluedStructure hπ data S r (j + 1 + m) hm =
      Spec.map (CommRingCat.ofHom (algebraMap S T₀)) := by
  rw [coefficientShearRetainedTensorChart, Category.assoc, coefficientShearGluedChart_structure]
  change (successiveCoefficientShearIso _ _ _ _ _ _ _ _).inv ≫
    Spec.map (CommRingCat.ofHom (algebraMap S _)) = _
  rw [← successiveCoefficientShearIso_structure, Iso.inv_hom_id_assoc]

/-- The entire scale-one conic retains its original coefficient leg. -/
theorem coefficientShearRetainedScaleOneConic_structure :
    coefficientShearRetainedScaleOneConic hπ data S r j hj m hm hs hp h3 h4 hr ≫
        coefficientShearGluedStructure hπ data S r (j + 1 + m) hm = conicStructure a c₀ := by
  rw [coefficientShearRetainedScaleOneConic, Category.assoc,
    coefficientShearRetainedScaleOneTensor_structure hπ data S r j hj m hm,
    tensorShearScaleOneConicImmersion_eq_spec]
  exact terminalComponent_algebra_structure _

/-- The separate scale-one conic projects through every original integral chart function. -/
theorem coefficientShearRetainedScaleOneConic_projection :
    coefficientShearRetainedScaleOneConic hπ data S r j hj m hm hs hp h3 h4 hr ≫ P =
      Spec.map (CommRingCat.ofHom (c).toRingHom) ≫ F := by
  rw [coefficientShearRetainedScaleOneConic, Category.assoc,
    coefficientShearRetainedTensorChart_projection hπ data S r j hj m hm,
    tensorShearScaleOneConicImmersion_eq_spec, ← Category.assoc]
  apply congrArg (· ≫ F)
  exact originalShearScaleOneConicMap_spec W (π ^ (start + j)) π
    (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr

end FLT.Mazur.WeierstrassDividedDepth
