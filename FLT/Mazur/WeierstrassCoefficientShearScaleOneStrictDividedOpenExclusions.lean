/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootTerminalZeroComponents
public import FLT.Mazur.WeierstrassCoefficientShearTerminalEquationCharts
public import FLT.Mazur.WeierstrassCoefficientShearScaleOneConicExclusions
public import FLT.Mazur.WeierstrassDividedOlderResidueInfinity
public import FLT.Mazur.ProjectiveLineMapOpenExclusion
public import FLT.Mazur.PolygonNodeWholeBranchCover
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic

/-!
# Scale-one strict terminal components exclude the exterior and infinity

Density of each full left chart and coverage by both whole node branches retain the origin.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (hs : algebraMap R S (π ^ (start + j)) = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (h6 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S (Data.b6 d)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "hsNext" => show algebraMap R S (π ^ (start + (j + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, hp, mul_zero]
local notation "conic" => coefficientShearRetainedScaleOneConic hπ data S r j hj 0 hj
  hs hp h3 h4 hr
local notation "E" => conicZeroAffineIso c h6
local notation "P₁" => (E).hom ≫ coefficientConicFirstParameter (U).a₁ c hu conic
local notation "P₂" => (E).hom ≫ coefficientConicSecondParameter (U).a₁ c hu conic
local notation "N" => coefficientShearTerminalNode
  hπ data S r (j + 1) hj hsNext h3 h4 h6 hr a ha
local notation "B₁" => coefficientShearTerminalFirstBranch
  hπ data S r (j + 1) hj hsNext h3 h4 h6 hr a ha
local notation "B₂" => coefficientShearTerminalSecondBranch
  hπ data S r (j + 1) hj hsNext h3 h4 h6 hr a ha
local notation "G" => coefficientShearGluedIso hπ data S r (j + 1) hj
local notation "ψ" => tensorShearScaleOneTerminalNodeConicMap W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr h6 a ha
local notation "b" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "inc" => PrincipalOpenTransport.inclusion (conicT (U).a₁ c)
local notation "F" => tensorShearScaleOneConicBoundaryIso W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr
local notation "T" => tensorShearTerminalNodeEquiv W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hp h3 h4 hr h6 a ha

local notation "C₁" => coefficientShearRootTerminalZeroFirstComponent
  hπ data S r j hj hs hp h3 h4 h6 hr a ha
local notation "C₂" => coefficientShearRootTerminalZeroSecondComponent
  hπ data S r j hj hs hp h3 h4 h6 hr a ha
local notation "tensorConic" => tensorShearScaleOneConicImmersion W (π ^ (start + j)) π
  (d).b3 (d).b4 (d).b6 S r hs hp h3 h4 hr
local notation "old" => olderGlobalTensorChart hπ data S j hj 0 hj
local notation "A" => coefficientShearAtlasMap hπ data S r (j + 1) hj
local notation "L" => coefficientShearTerminalEquationIso
  data S r (j + 1) hj hsNext h3 h4 h6 hr a ha

/-- Every divided-chart point lies on one of the two full terminal components. -/
theorem coefficientShearScaleOneStrictDivided_range_subset_components :
    Set.range (A (.inl 1)) ⊆ Set.range (C₁ ≫ (G).hom) ∪ Set.range (C₂ ≫ (G).hom) := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨z, rfl⟩ := (L).hom.homeomorph.surjective z
  have h₁ : PolygonCyclicAtlas.firstBranch S ≫ (L).hom ≫ A (.inl 1) =
      ProjectiveLine.right S ≫ C₂ ≫ (G).hom := by
    rw [← coefficientShearGluedIso_chart, ← Category.assoc (L).hom,
      coefficientShearTerminalEquationIso_chart]
    rw [coefficientShearRootTerminalZeroSecondComponent_right_assoc]
    rfl
  have h₂ : PolygonCyclicAtlas.secondBranch S ≫ (L).hom ≫ A (.inl 1) =
      ProjectiveLine.right S ≫ C₁ ≫ (G).hom := by
    rw [← coefficientShearGluedIso_chart, ← Category.assoc (L).hom,
      coefficientShearTerminalEquationIso_chart]
    rw [coefficientShearRootTerminalZeroFirstComponent_right_assoc]
    rfl
  rcases PolygonNodeBranches.wholeBranches_cover S z with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · exact Or.inr ⟨ProjectiveLine.right S v, (congrArg (fun f => f v) h₁).symm⟩
  · exact Or.inl ⟨ProjectiveLine.right S v, (congrArg (fun f => f v) h₂).symm⟩

include hs hp h3 h4 h6 hr a ha

/-- The full divided node excludes any open already excluded by the whole retained conic. -/
theorem coefficientShearScaleOneStrictDivided_disjoint_of_conic
    {X : Scheme.{u}} (f : X ⟶ finiteGlobalTensorModel hπ data S (j + 1) hj)
    [IsOpenImmersion f]
    (h : Disjoint (Set.range (tensorConic ≫ old)) (Set.range f)) :
    Disjoint (Set.range (A (.inl 1))) (Set.range f) := by
  have hrconic : conic ≫ (G).hom = tensorConic ≫ old := by
    rw [coefficientShearRetainedScaleOneConic, Category.assoc,
      coefficientShearRetainedTensorChart_original hπ data S r j hj 0 hj]
  have h₁ : Disjoint (Set.range (C₁ ≫ (G).hom)) (Set.range f) := by
    apply ProjectiveLine.map_range_open_disjoint_of_left S
    rw [coefficientShearRootTerminalZeroFirstComponent_left_assoc]
    apply h.mono_left
    rintro _ ⟨z, rfl⟩
    simp only [coefficientConicFirstParameter, Category.assoc, hrconic]
    exact ⟨_, rfl⟩
  have h₂ : Disjoint (Set.range (C₂ ≫ (G).hom)) (Set.range f) := by
    apply ProjectiveLine.map_range_open_disjoint_of_left S
    rw [coefficientShearRootTerminalZeroSecondComponent_left_assoc]
    apply h.mono_left
    rintro _ ⟨z, rfl⟩
    simp only [coefficientConicSecondParameter, Category.assoc, hrconic]
    exact ⟨_, rfl⟩
  exact (Set.disjoint_union_left.mpr ⟨h₁, h₂⟩).mono_left
    (coefficientShearScaleOneStrictDivided_range_subset_components
      hπ data S r j hj hs hp h3 h4 h6 hr a ha)

/-- The complete terminal node misses the original preceding exterior. -/
theorem coefficientShearScaleOneStrictDivided_precedingExterior_disjoint :
    Disjoint (Set.range (A (.inl 1)))
      (Set.range (olderGlobalExteriorTensorChart hπ data S j hj 0 hj)) := by
  apply coefficientShearScaleOneStrictDivided_disjoint_of_conic
    hπ data S r j hj hs hp h3 h4 h6 hr a ha
  exact (coefficientShearScaleOneConicExterior_disjoint
    hπ data S r j hj 0 hj hs hp h3 h4 hr).symm

/-- At scale one the entire divided node misses infinity. -/
theorem coefficientShearScaleOneStrictDivided_infinity_disjoint :
    Disjoint (Set.range (A (.inl 1)))
      (Set.range (finiteInfinityTensorChart hπ data S (j + 1) hj)) := by
  apply coefficientShearScaleOneStrictDivided_disjoint_of_conic
    hπ data S r j hj hs hp h3 h4 h6 hr a ha
  exact (coefficientShearScaleOneConicInfinity_disjoint
    hπ data S r j hj 0 hj hs hp h3 h4 hr).symm

end FLT.Mazur.WeierstrassDividedDepth
