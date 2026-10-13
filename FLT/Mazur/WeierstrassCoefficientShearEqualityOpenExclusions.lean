/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearEqualityChartParameters
public import FLT.Mazur.WeierstrassCoefficientShearConicExteriorDisjoint
public import FLT.Mazur.WeierstrassCoefficientShearRetainedReconstruction
public import FLT.Mazur.ProjectiveLineOpenChartExclusion
public import FLT.Mazur.WeierstrassDividedOlderResidueInfinity
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Open exclusions for the full arbitrary-root equality component

The original conic is a nonempty open of the completed projective component.
Its tensor reconstruction excludes both the preceding exterior and infinity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (hs : algebraMap R S (π ^ (start + j)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (hc : IsUnit (algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6))
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S (Data.b6 d)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "hsNext" => show algebraMap R S (π ^ (start + (j + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, hp, mul_zero]
local notation "conic" => coefficientShearRetainedConic hπ data S r (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j)) hs hp h3 h4 hr
local notation "G" => coefficientShearGluedIso hπ data S r (j + 1) hj
local notation "C" => coefficientShearRootEqualityComponent
  hπ data S r j hj hs hp h3 h4 hc hr a ha
local notation "q" => coefficientShearEqualityConicParameter
  data S r j hj hs hp h3 h4 hc hr a ha
local notation "tensorConic" => tensorShearConicImmersion W (π ^ (start + j)) π
  (d).b3 (d).b4 (d).b6 S r hs hp h3 h4 hr
local notation "old" => olderGlobalTensorChart hπ data S j hj 0 hj

/-- The full conic reconstructs its original tensor immersion at the final stage. -/
@[reassoc] theorem coefficientShearEqualityConic_reconstruction :
    q ≫ C ≫ (G).hom = tensorConic ≫ old := by
  rw [← Category.assoc, coefficientShearEqualityConicParameter_component]
  rw [← coefficientShearRetainedTensorChart_conic, Category.assoc,
    coefficientShearRetainedTensorChart_original hπ data S r j hj 0 hj]

/-- Testing the full conic suffices to exclude an open from the complete component. -/
theorem coefficientShearEqualityComponent_disjoint_of_conic
    {X : Scheme.{u}} (f : X ⟶ finiteGlobalTensorModel hπ data S (j + 1) hj)
    [IsOpenImmersion f]
    (h : Disjoint (Set.range (tensorConic ≫ old)) (Set.range f)) :
    Disjoint (Set.range (C ≫ (G).hom)) (Set.range f) := by
  let p := Spec.map (CommRingCat.ofHom
    (conicFirstIncidencePoint (U).a₁ c hu).toRingHom)
  let _ : Nonempty (Spec (.of (ConicCoordinate (U).a₁ c))) :=
    Nonempty.map p inferInstance
  let _ : IsOpenImmersion q := by
    unfold coefficientShearEqualityConicParameter
    infer_instance
  apply ProjectiveLine.map_range_open_disjoint_of_chart S q (C ≫ (G).hom) f
  simpa only [coefficientShearEqualityConic_reconstruction] using h

/-- The whole arbitrary-root equality component misses the original preceding exterior. -/
theorem coefficientShearEqualityComponent_precedingExterior_disjoint :
    Disjoint (Set.range (C ≫ (G).hom))
      (Set.range (olderGlobalExteriorTensorChart hπ data S j hj 0 hj)) := by
  apply coefficientShearEqualityComponent_disjoint_of_conic
    hπ data S r j hj hs hp h3 h4 hc hr a ha
  exact (coefficientShearConicExterior_disjoint
    hπ data S r j hj 0 hj hs hp h3 h4 hr).symm

/-- At positive scale the complete equality component has empty infinity intersection. -/
theorem coefficientShearEqualityComponent_infinity_disjoint (hpos : 0 < start + j) :
    Disjoint (Set.range (C ≫ (G).hom))
      (Set.range (finiteInfinityTensorChart hπ data S (j + 1) hj)) := by
  apply coefficientShearEqualityComponent_disjoint_of_conic
    hπ data S r j hj hs hp h3 h4 hc hr a ha
  apply (olderGlobalResidue_infinity_disjoint S hπ data j hj 0 hj hp hpos).mono_left
  rintro _ ⟨z, rfl⟩
  exact ⟨tensorConic z, rfl⟩

end FLT.Mazur.WeierstrassDividedDepth
