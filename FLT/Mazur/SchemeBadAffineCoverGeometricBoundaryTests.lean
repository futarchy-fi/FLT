/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeBadAffineCoverBoundaryUnits
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Geometric tests for exact bad-chart boundary equations

Testing all algebraically closed boundary scalar values is enough to construct
finite exact-kernel unit equations. The fields are derived from actual maximal
ideals of the original boundary ring; no finite type hypothesis on that ring is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeBadAffineCover
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R T : Type} [CommRing R] [CommRing T] {X : Scheme}
  [NoetherianSpace X] (s : R →+* Γ(X, ⊤)) (O : X.Opens) (κ : R →+* T)

/-- Empty obstructions have a nonvanishing exact kernel scalar at every field-valued boundary. -/
theorem boundaryChart_field_separator (i : (badCover O).I₀)
    (h : IsEmpty (boundaryChartObstruction s O κ i))
    {K : Type} [Field K] (φ : T →+* K) :
    ∃ r : R, badChartScalar s O i r = 0 ∧ φ (κ r) ≠ 0 := by
  by_contra hn
  push Not at hn
  have hle : boundaryChartIdeal s O κ i ≤ RingHom.ker φ := by
    apply Ideal.map_le_iff_le_comap.mpr
    exact hn
  rw [(boundaryChartObstruction_empty_iff s O κ i).mp h] at hle
  have he : φ 1 = 0 := hle (show (1 : T) ∈ (⊤ : Ideal T) from trivial)
  exact one_ne_zero ((map_one φ).symm.trans he)

/-- Algebraically closed boundary tests detect emptiness of the full closed obstruction. -/
theorem boundaryChart_empty_iff_geometric_separators (i : (badCover O).I₀) :
    IsEmpty (boundaryChartObstruction s O κ i) ↔
      ∀ (K : Type) [Field K] [IsAlgClosed K] (φ : T →+* K),
        ∃ r : R, badChartScalar s O i r = 0 ∧ φ (κ r) ≠ 0 := by
  refine ⟨fun h K _ _ φ ↦ boundaryChart_field_separator s O κ i h φ, ?_⟩
  intro h
  apply (boundaryChartObstruction_empty_iff s O κ i).mpr
  by_contra hn
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hn
  let _ := hM
  let _ := Ideal.Quotient.field M
  let K := AlgebraicClosure (T ⧸ M)
  let φ : T →+* K := (algebraMap (T ⧸ M) K).comp (Ideal.Quotient.mk M)
  obtain ⟨r, hr, hφ⟩ := h K φ
  apply hφ
  have hm : κ r ∈ M := hle (Ideal.mem_map_of_mem κ hr)
  change algebraMap (T ⧸ M) K (Ideal.Quotient.mk M (κ r)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm, map_zero]

/-- Geometric separation constructs a finite unit equation on each actual bad chart. -/
theorem boundaryChart_finite_equation_of_geometric_separators (i : (badCover O).I₀)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (φ : T →+* K),
      ∃ r : R, badChartScalar s O i r = 0 ∧ φ (κ r) ≠ 0) :
    ∃ (n : ℕ) (a : Fin n → R) (b : Fin n → T),
      (∀ j, badChartScalar s O i (a j) = 0) ∧ ∑ j, b j * κ (a j) = 1 :=
  (boundaryChart_empty_iff_finite_equation s O κ i).mp
    ((boundaryChart_empty_iff_geometric_separators s O κ i).mpr h)

/-- All geometric chart tests produce full original denominators in the original boundary ring. -/
theorem boundary_equation_of_geometric_separators
    (h : ∀ (i : (badCover O).I₀) (K : Type) [Field K] [IsAlgClosed K] (φ : T →+* K),
      ∃ r : R, badChartScalar s O i r = 0 ∧ φ (κ r) ≠ 0) :
    ∃ (n : ℕ) (a : Fin n → R) (b : Fin n → T),
      (∀ j, X.basicOpen (s (a j)) ≤ O) ∧ ∑ j, b j * κ (a j) = 1 :=
  exists_boundary_denominator_equation_of_chart_equations s O κ
    (fun i ↦ boundaryChart_finite_equation_of_geometric_separators s O κ i (h i))

end FLT.Mazur.SchemeBadAffineCover
