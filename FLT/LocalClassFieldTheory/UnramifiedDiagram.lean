/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedGaloisLimit
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# The degree-indexed unramified diagram

Positive degrees are ordered by divisibility. The corresponding finite Galois
fields inside the unramified union form a final functor, so their opposite
category is an initial index category for the Galois inverse limit.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

/-- Positive degrees, ordered by divisibility rather than numerical size. -/
structure UnramifiedIndex where
  /-- The positive degree. -/
  degree : ℕ+

instance : PartialOrder UnramifiedIndex where
  le n m := n.degree ∣ m.degree
  le_refl _ := dvd_refl _
  le_trans _ _ _ := dvd_trans
  le_antisymm := by
    rintro ⟨n⟩ ⟨m⟩ h h'
    exact congrArg UnramifiedIndex.mk (PNat.dvd_antisymm h h')

instance : Nonempty UnramifiedIndex := ⟨⟨1⟩⟩

instance : IsDirectedOrder UnramifiedIndex where
  directed n m := ⟨⟨n.degree * m.degree⟩, dvd_mul_right _ _, dvd_mul_left _ _⟩

variable (R K C : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]

/-- A degree-indexed stage, regarded as a finite Galois field inside the union. -/
def unramifiedFiniteStage (n : UnramifiedIndex) :
    FiniteGaloisIntermediateField K (maximalUnramified R K C) := by
  let E := unramifiedStage R K C n.degree
  let h := unramifiedStage_le_maximalUnramified R K C n.degree
  let e := IntermediateField.restrictAlgEquiv h
  let := (unramifiedStage_isUnramified R K C n.degree).1
  let := (unramifiedStage_isUnramified R K C n.degree).normal
  let : FiniteDimensional K (IntermediateField.restrict h) := e.toLinearEquiv.finiteDimensional
  let : Normal K (IntermediateField.restrict h) := Normal.of_algEquiv e
  exact { toIntermediateField := IntermediateField.restrict h, isGalois := ⟨⟩ }

/-- Membership in the reindexed field is membership in the original stage. -/
theorem mem_unramifiedFiniteStage (n : UnramifiedIndex) (x : maximalUnramified R K C) :
    x ∈ (unramifiedFiniteStage R K C n).toIntermediateField ↔
      x.val ∈ unramifiedStage R K C n.degree :=
  IntermediateField.mem_restrict _ x

/-- Divisibility of degrees induces inclusion of the finite fields. -/
theorem unramifiedFiniteStage_monotone : Monotone (unramifiedFiniteStage R K C) := by
  intro n m h x hx
  apply (mem_unramifiedFiniteStage R K C m x).mpr
  exact (unramifiedStage_le_iff R K C n.degree m.degree).mpr (PNat.dvd_iff.mp h)
    ((mem_unramifiedFiniteStage R K C n x).mp hx)

/-- The positive-degree indexing functor into all finite Galois fields. -/
def unramifiedStageFunctor :
    UnramifiedIndex ⥤ FiniteGaloisIntermediateField K (maximalUnramified R K C) :=
  (unramifiedFiniteStage_monotone R K C).functor

/-- Every finite Galois field in the union is dominated by a degree-indexed stage. -/
instance unramifiedStageFunctor_final : (unramifiedStageFunctor R K C).Final := by
  apply (unramifiedFiniteStage_monotone R K C).final_functor_iff.mpr
  intro E
  let := (IntermediateField.liftAlgEquiv E.toIntermediateField).toLinearEquiv.finiteDimensional
  obtain ⟨n, hn⟩ := exists_unramifiedStage_of_finite_le R K C
    (IntermediateField.lift E.toIntermediateField) (IntermediateField.lift_le _)
  refine ⟨⟨n⟩, fun x hx => (mem_unramifiedFiniteStage R K C ⟨n⟩ x).mpr ?_⟩
  exact hn ((IntermediateField.mem_lift x).mpr hx)

/-- The inverse system of finite Galois groups indexed by positive degrees. -/
def unramifiedDegreeDiagram : UnramifiedIndexᵒᵖ ⥤ ProfiniteGrp :=
  (unramifiedStageFunctor R K C).op ⋙
    InfiniteGalois.asProfiniteGaloisGroupFunctor K (maximalUnramified R K C)

end LocalClassFieldTheory
