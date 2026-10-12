/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Grassmannian
public import Mathlib.LinearAlgebra.Prod

/-!
# Split-coordinate quotient Grassmannian charts

A matrix from the complementary summand to the selected rank-d summand gives
the normalized quotient `(x,y) ↦ x + A(y)`. Its kernel is a genuine Grassmannian
point and the selected summand maps isomorphically onto the quotient.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable (S : Type*) [CommRing S] (V : Type*) [AddCommGroup V] [Module S V] (d : ℕ)

/-- The chart where the selected rank-d summand is a basis of the quotient. -/
def SplitChart :=
  {N : Module.Grassmannian S ((Fin d → S) × V) d //
    Function.Bijective (N.toSubmodule.mkQ.comp (LinearMap.inl S (Fin d → S) V))}

variable {S V d}

/-- The normalized quotient determined by complementary coordinates. -/
def splitChartEvaluation (A : V →ₗ[S] (Fin d → S)) :
    ((Fin d → S) × V) →ₗ[S] (Fin d → S) := LinearMap.coprod LinearMap.id A

/-- The selected summand is a section of normalized evaluation. -/
theorem splitChartEvaluation_section (A : V →ₗ[S] (Fin d → S)) :
    (splitChartEvaluation A).comp (LinearMap.inl S (Fin d → S) V) = LinearMap.id := by
  ext x i
  simp [splitChartEvaluation]

/-- Every coordinate matrix defines a surjective quotient. -/
theorem splitChartEvaluation_surjective (A : V →ₗ[S] (Fin d → S)) :
    Function.Surjective (splitChartEvaluation A) :=
  Function.HasRightInverse.surjective
    ⟨LinearMap.inl S (Fin d → S) V, LinearMap.congr_fun (splitChartEvaluation_section A)⟩

/-- The quotient of the ambient module by the graph relations is the selected free module. -/
def splitChartQuotientEquiv (A : V →ₗ[S] (Fin d → S)) :
    (((Fin d → S) × V) ⧸ (splitChartEvaluation A).ker) ≃ₗ[S] (Fin d → S) :=
  (splitChartEvaluation A).quotKerEquivOfSurjective (splitChartEvaluation_surjective A)

/-- A coordinate matrix gives an actual quotient Grassmannian point. -/
def splitChartGrassmannian (A : V →ₗ[S] (Fin d → S)) :
    Module.Grassmannian S ((Fin d → S) × V) d := by
  let e := splitChartQuotientEquiv A
  refine { toSubmodule := (splitChartEvaluation A).ker
           finite_quotient := Module.Finite.equiv e.symm
           projective_quotient := Module.Projective.of_equiv e.symm
           rankAtStalk_eq := ?_ }
  intro p
  let _ : Nontrivial S := ⟨⟨1, 0, fun h ↦ p.isPrime.one_notMem
    (by rw [h]; exact p.asIdeal.zero_mem)⟩⟩
  rw [congrFun (Module.rankAtStalk_eq_of_equiv e) p,
    Module.rankAtStalk_eq_finrank_of_free]
  simp

/-- The selected summand maps bijectively onto the constructed quotient. -/
theorem splitChartGrassmannian_mem (A : V →ₗ[S] (Fin d → S)) :
    Function.Bijective ((splitChartGrassmannian A).toSubmodule.mkQ.comp
      (LinearMap.inl S (Fin d → S) V)) := by
  have h : (splitChartQuotientEquiv A).toLinearMap.comp
      ((splitChartGrassmannian A).toSubmodule.mkQ.comp
        (LinearMap.inl S (Fin d → S) V)) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change (splitChartEvaluation A).quotKerEquivOfSurjective (splitChartEvaluation_surjective A)
      (Submodule.Quotient.mk (x, 0)) = x
    rw [LinearMap.quotKerEquivOfSurjective_apply_mk]
    simp [splitChartEvaluation]
  have hb : Function.Bijective ((splitChartQuotientEquiv A).toLinearMap.comp
      ((splitChartGrassmannian A).toSubmodule.mkQ.comp
        (LinearMap.inl S (Fin d → S) V))) := by
    rw [h]
    exact Function.bijective_id
  refine ⟨fun x y hxy ↦ hb.1 (congrArg (splitChartQuotientEquiv A) hxy), ?_⟩
  intro x
  obtain ⟨y, hy⟩ := hb.2 (splitChartQuotientEquiv A x)
  exact ⟨y, (splitChartQuotientEquiv A).injective hy⟩

/-- The chart point attached to a complementary-coordinate matrix. -/
def splitChartOfCoordinates (A : V →ₗ[S] (Fin d → S)) : SplitChart S V d :=
  ⟨splitChartGrassmannian A, splitChartGrassmannian_mem A⟩

end FLT.Mazur.GrassmannianChart
