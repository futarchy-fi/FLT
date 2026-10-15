/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOpenEnvelopeInterior
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The exact remaining obstruction outside a proper envelope core

An actual proper open core gives an open full-fiber condition. The full
original interior is its intersection with the complement of the closure of
the excluded residual image. At an original full fiber, avoiding that closure
is necessary and sufficient. No properness of the residual projection is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ProperCoreResidualInterior
open SchemeOpenEnvelope
universe u
variable {X Y : Scheme.{u}} (π : Y ⟶ X) (U T : Y.Opens)

/-- The original source image of excluded points outside the chosen proper core. -/
def residualBadImage : Set X := π '' {y : Y | y ∉ U ∧ y ∉ T}

/-- Original fullness is exactly core fullness together with absence of residual bad points. -/
theorem fullFiberLocus_eq :
    fullFiberLocus π U = fullFiberLocus (T.ι ≫ π) (T.ι ⁻¹ᵁ U) ∩
      (residualBadImage π U T)ᶜ := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · apply (mem_fullFiberLocus _ _ x).mpr
      intro y hy
      exact (mem_fullFiberLocus π U x).mp hx y.val hy
    · rintro ⟨y, hy, he⟩
      exact hy.1 ((mem_fullFiberLocus π U x).mp hx y he)
  · rintro ⟨hc, hr⟩
    apply (mem_fullFiberLocus π U x).mpr
    intro y hy
    by_cases ht : y ∈ T
    · exact (mem_fullFiberLocus _ _ x).mp hc ⟨y, ht⟩ hy
    · by_contra hu
      exact hr ⟨y, ⟨hu, ht⟩, hy⟩

variable [IsProper (T.ι ≫ π)]

/-- The complete original interior has an exact closed-obstruction formula. -/
theorem fullFiberInterior_eq :
    (fullFiberInterior π U : Set X) =
      (fullFiberOpen (T.ι ≫ π) (T.ι ⁻¹ᵁ U) (T.ι ≫ π).isClosedMap : Set X) ∩
      (closure (residualBadImage π U T))ᶜ := by
  change interior (fullFiberLocus π U) = _
  rw [fullFiberLocus_eq π U T, interior_inter, interior_compl]
  exact congrArg (· ∩ (closure (residualBadImage π U T))ᶜ)
    (fullFiberOpen (T.ι ≫ π) (T.ι ⁻¹ᵁ U) (T.ι ≫ π).isClosedMap).isOpen.interior_eq

/-- At an original full fiber, only the closure of the residual bad image can obstruct interior. -/
theorem mem_fullFiberInterior_iff (x : X) (hx : x ∈ fullFiberLocus π U) :
    x ∈ fullFiberInterior π U ↔ x ∉ closure (residualBadImage π U T) := by
  have hc := ((Set.ext_iff.mp (fullFiberLocus_eq π U T)) x).mp hx
  rw [show x ∈ fullFiberInterior π U ↔
    x ∈ (fullFiberInterior π U : Set X) from Iff.rfl, fullFiberInterior_eq π U T]
  exact and_iff_right hc.1

/-- Closed residual bad images automatically discharge the remaining obstruction at full fibers. -/
theorem mem_fullFiberInterior_of_residualClosed
    (hr : IsClosed (residualBadImage π U T)) (x : X) (hx : x ∈ fullFiberLocus π U) :
    x ∈ fullFiberInterior π U := by
  apply (mem_fullFiberInterior_iff π U T x hx).mpr
  rw [hr.closure_eq]
  exact ((Set.ext_iff.mp (fullFiberLocus_eq π U T)) x).mp hx |>.2

/-- A finite family avoiding the residual obstruction has one actual original denominator. -/
theorem exists_denominator [IsAffine X] (F : Set X) (hF : F.Finite)
    (hFU : F ⊆ fullFiberLocus π U)
    (hr : Disjoint F (closure (residualBadImage π U T))) :
    ∃ r : Γ(X, ⊤), F ⊆ X.basicOpen r ∧ r ∈ denominatorIdeal π.appTop.hom U := by
  apply exists_fullFiberInterior_coefficient π U F hF
  intro x hx
  exact (mem_fullFiberInterior_iff π U T x (hFU hx)).mpr
    (fun h ↦ Set.disjoint_left.mp hr hx h)

end FLT.Mazur.ProperCoreResidualInterior
