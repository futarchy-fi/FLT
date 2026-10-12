/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianDeterminantChartSections
public import FLT.Mazur.GrassmannianAmbientGluedBase
public import FLT.Mazur.AffineBaseSectionAlgebra

/-!
# Determinant coordinates on arbitrary common scheme tests

The exact chart pullback gives the common test its original overlap map.
Pulling the polynomial identity back gives a multiplicative section identity
and a unit on any scheme test, including nonaffine and nonreduced tests.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
set_option backward.isDefEq.respectTransparency false
open Approximation
universe u
variable {R M ι : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] {d : ℕ}

/-- Evaluating affine coordinates commutes with a spectrum morphism. -/
theorem determinantSpectrum_evaluate {A B : Type u} [CommRing A] [CommRing B]
    {T : Scheme.{u}} (a : T ⟶ Spec (.of B)) (r : A →+* B) (s : A) :
    affineBaseSectionMap (a ≫ Spec.map (CommRingCat.ofHom r)) s =
      affineBaseSectionMap a (r s) := by
  unfold affineBaseSectionMap
  rw [Scheme.Hom.comp_appTop]
  change a.appTop ((Spec.map (CommRingCat.ofHom r)).appTop
    ((Scheme.ΓSpecIso (.of A)).inv s)) = _
  exact congrArg (fun t ↦ a.appTop t)
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom r)) s).symm

/-- A selected determinant pulled back from its original affine chart. -/
def determinantTestSection (i k : AmbientChartIndex R M ι d)
    {T : Scheme.{u}} (a : T ⟶ indexedChartScheme i) : Γ(T, ⊤) :=
  affineBaseSectionMap a (determinantChartSection i k)

/-- The original distinguished section stays one on every test. -/
@[simp] theorem determinantTestSection_self (i : AmbientChartIndex R M ι d)
    {T : Scheme.{u}} (a : T ⟶ indexedChartScheme i) :
    determinantTestSection i i a = 1 := by
  unfold determinantTestSection
  rw [determinantChartSection_self, map_one]

variable (i j : AmbientChartIndex R M ι d) {T : Scheme.{u}}
  (a : T ⟶ indexedChartScheme i) (b : T ⟶ indexedChartScheme j)
  (h : a ≫ ambientGrassmannianChart R M ι d i =
    b ≫ ambientGrassmannianChart R M ι d j)

/-- Equal original chart classifications construct the actual overlap morphism. -/
def determinantCommonTestLift : T ⟶ indexedOverlapScheme i j :=
  (ambientGrassmannianChart_isPullback R M ι d i j).lift a b h

/-- The constructed overlap map retains the first original chart morphism. -/
@[reassoc] theorem determinantCommonTestLift_first :
    determinantCommonTestLift i j a b h ≫ indexedOverlapInclusion i j = a :=
  (ambientGrassmannianChart_isPullback R M ι d i j).lift_fst _ _ _

/-- The constructed overlap map retains the second original chart morphism. -/
@[reassoc] theorem determinantCommonTestLift_second :
    determinantCommonTestLift i j a b h ≫ indexedChartTransition i j = b :=
  (ambientGrassmannianChart_isPullback R M ι d i j).lift_snd _ _ _

include h in
/-- Double-chart membership makes the original selected determinant a unit on the test. -/
theorem determinantTestSection_isUnit : IsUnit (determinantTestSection i j a) := by
  rw [← determinantCommonTestLift_first i j a b h]
  unfold determinantTestSection
  dsimp only [indexedOverlapInclusion, principalOverlapInclusion, Spec.algebraMap,
    indexedChartTransition, localizedChartTransitionScheme]
  rw [determinantSpectrum_evaluate, determinantChartSection_overlap]
  exact (determinantOverlapUnit (ambientChartChange i j)).isUnit.map
    (affineBaseSectionMap (determinantCommonTestLift i j a b h))

include h in
/-- All determinant coordinates obey the same transition on the whole common scheme test. -/
theorem determinantTestSection_transition (k : AmbientChartIndex R M ι d) :
    determinantTestSection i k a =
      determinantTestSection i j a * determinantTestSection j k b := by
  conv_lhs => rw [← determinantCommonTestLift_first i j a b h]
  conv_rhs =>
    arg 1
    rw [← determinantCommonTestLift_first i j a b h]
  conv_rhs =>
    arg 2
    rw [← determinantCommonTestLift_second i j a b h]
  unfold determinantTestSection
  dsimp only [indexedOverlapInclusion, principalOverlapInclusion, Spec.algebraMap,
    indexedChartTransition, localizedChartTransitionScheme]
  rw [determinantSpectrum_evaluate, determinantSpectrum_evaluate,
    determinantSpectrum_evaluate, determinantChartSection_transition,
    determinantChartSection_overlap, map_mul]
  rfl

end FLT.Mazur.GrassmannianChart
