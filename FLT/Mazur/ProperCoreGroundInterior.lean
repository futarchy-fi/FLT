/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperCoreResidualInterior
public import FLT.Mazur.CartesianNormFullFiber

/-!
# Exact local residual obstruction after Cartesian ground change

A proper open core in the full changed envelope detects the original interior
at any lift through an open source comparison. The comparison need not cover
the whole source. Different original points may use different such squares.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.ProperCoreGroundInterior
open SchemeOpenEnvelope ProperCoreResidualInterior
universe u
variable {E F X Y : Scheme.{u}} {g : E ⟶ F} {p : E ⟶ X} {q : F ⟶ Y} {v : X ⟶ Y}
  (H : IsPullback g p q v) (U : F.Opens) (T : E.Opens)
  [IsProper (T.ι ≫ p)] (hv : IsOpenMap v)

include H hv

/-- One lifted full fiber detects original interior by the exact changed residual obstruction. -/
theorem original_mem_iff (x : X) (hx : v x ∈ fullFiberLocus q U) :
    v x ∈ fullFiberInterior q U ↔
      x ∉ closure (residualBadImage p (g ⁻¹ᵁ U) T) := by
  have hx' : x ∈ fullFiberLocus p (g ⁻¹ᵁ U) := by
    rw [fullFiberLocus_baseChange H U]
    exact hx
  have hi := fullFiberInterior_baseChange H U hv
  rw [← show x ∈ fullFiberInterior p (g ⁻¹ᵁ U) ↔
    v x ∈ fullFiberInterior q U from by rw [hi]; rfl]
  exact mem_fullFiberInterior_iff p (g ⁻¹ᵁ U) T x hx'

/-- Closedness of the actual residual bad image suffices at any reached original full fiber. -/
theorem original_mem_of_closed_residual
    (hr : IsClosed (residualBadImage p (g ⁻¹ᵁ U) T))
    (y : Y) (hy : y ∈ fullFiberLocus q U) (hlift : y ∈ Set.range v) :
    y ∈ fullFiberInterior q U := by
  obtain ⟨x, rfl⟩ := hlift
  apply (original_mem_iff H U T hv x hy).mpr
  rw [hr.closure_eq]
  rintro ⟨e, he, hx⟩
  apply he.1
  have hy' : x ∈ fullFiberLocus p (g ⁻¹ᵁ U) := by
    rw [fullFiberLocus_baseChange H U]
    exact hy
  exact (mem_fullFiberLocus p (g ⁻¹ᵁ U) x).mp hy' e hx

/-- Finite original full-fiber sets get one denominator from locally unobstructed lifts. -/
theorem exists_original_denominator [IsAffine Y] (A : Set Y) (hA : A.Finite)
    (hAU : A ⊆ fullFiberLocus q U)
    (hlift : ∀ y ∈ A, ∃ x : X, v x = y ∧
      x ∉ closure (residualBadImage p (g ⁻¹ᵁ U) T)) :
    ∃ r : Γ(Y, ⊤), A ⊆ Y.basicOpen r ∧ r ∈ denominatorIdeal q.appTop.hom U := by
  apply exists_fullFiberInterior_coefficient q U A hA
  intro y hy
  obtain ⟨x, rfl, hx⟩ := hlift y hy
  exact (original_mem_iff H U T hv x (hAU hy)).mpr hx

end FLT.Mazur.ProperCoreGroundInterior
