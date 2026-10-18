/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedGlobalCoverage
public import Mathlib.AlgebraicGeometry.Morphisms.LocalIso

/-!
# The complete original revised comparison is a local isomorphism

Every full original chart embeds in the independent target. Combined with
surjectivity, this reduces the global isomorphism to reflection of intersections.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "G" => arithmeticFirstOriginalRevisedChart hπ data H j hj u hu
local notation "F" => arithmeticFirstOriginalRevisedGlobalMap hπ data H j hj u hu
local notation "a" => arithmeticLabeledAtlasMap hπ data H 1 (j + 1) hj
local notation "U" => arithmeticLabeledOpenCover hπ data H 1 (j + 1) hj

/-- Each full original label embeds under its concrete comparison map. -/
instance arithmeticFirstOriginalRevisedChart_isOpenImmersion
    (i : ArithmeticChartLabel (j + 1)) : IsOpenImmersion (G i) := by
  cases i with
  | infinity =>
    change IsOpenImmersion (arithmeticOriginalRevisedTensorInfinityMap data H 1 j hj u hu)
    infer_instance
  | initial b =>
    change IsOpenImmersion (arithmeticOriginalRevisedInitialMap data H 1 j hj u hu b)
    infer_instance
  | retained i b =>
    change IsOpenImmersion (arithmeticFirstOriginalRevisedRetainedMap hπ data H j hj u hu i b)
    infer_instance
  | terminal =>
    change IsOpenImmersion ((arithmeticFirstResidualAtlasIso hπ data H j hj u hu .terminal).hom ≫
      arithmeticRevisedPolygonTerminalChart data H 1 j hj u hu)
    infer_instance

/-- The global comparison is an open immersion on each full original cover member. -/
instance arithmeticFirstOriginalRevisedGlobalMap_chart_isOpenImmersion
    (i : ArithmeticChartLabel (j + 1)) : IsOpenImmersion (a i ≫ F) := by
  rw [arithmeticFirstOriginalRevisedGlobalMap_chart]
  infer_instance

/-- The complete first-order comparison is a Zariski local isomorphism. -/
instance arithmeticFirstOriginalRevisedGlobalMap_isLocalIso : IsLocalIso F := by
  rw [IsLocalIso.eq_sourceLocalClosure_isOpenImmersion]
  exact ⟨U, fun i ↦
    arithmeticFirstOriginalRevisedGlobalMap_chart_isOpenImmersion hπ data H j hj u hu i⟩

/-- Reflecting point equality will make the complete comparison an open immersion. -/
theorem arithmeticFirstOriginalRevisedGlobalMap_isOpenImmersion_of_injective
    (hi : Function.Injective F) : IsOpenImmersion F :=
  IsOpenImmersion.of_openCover_source F U hi
    (arithmeticFirstOriginalRevisedGlobalMap_chart_isOpenImmersion hπ data H j hj u hu)

/-- Surjectivity is proved, so reflection of intersections suffices for the global isomorphism. -/
theorem arithmeticFirstOriginalRevisedGlobalMap_isIso_of_injective
    (hi : Function.Injective F) : IsIso F := by
  let _ := arithmeticFirstOriginalRevisedGlobalMap_isOpenImmersion_of_injective
    hπ data H j hj u hu hi
  let _ : Epi (F).base := (TopCat.epi_iff_surjective _).mpr
    (arithmeticFirstOriginalRevisedGlobalMap_surjective hπ data H j hj u hu)
  exact IsOpenImmersion.isIso F

end FLT.Mazur.WeierstrassDividedDepth
