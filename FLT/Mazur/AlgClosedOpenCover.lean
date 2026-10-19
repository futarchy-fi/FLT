/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Detecting full scheme opens using points over an algebraically closed field

Finite type makes the source Jacobson. A nonempty closed complement would
contain a closed point, which is represented by a section over the base field.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FLT.Mazur.AlgClosedOpenCover

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  (s : X ⟶ Spec (.of K)) [LocallyOfFiniteType s]

include s

omit [IsAlgClosed K] in
/-- An open containing every closed point is the whole finite-type scheme. -/
theorem eq_top_of_closedPoints (U : X.Opens)
    (hU : ∀ x : X, IsClosed {x} → x ∈ U) : U = ⊤ := by
  let _ : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace s
  apply top_unique
  intro x _
  by_contra hx
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints
    (show ((U : Set X)ᶜ).Nonempty from ⟨x, hx⟩) U.isOpen.isClosed_compl.isLocallyClosed
  exact hy (hU y hyc)

/-- Coverage of base-field sections proves coverage of all scheme points. -/
theorem eq_top_of_sections (U : X.Opens)
    (hU : ∀ p : Spec (.of K) ⟶ X, p ≫ s = 𝟙 _ → Set.range p ⊆ U) : U = ⊤ := by
  apply eq_top_of_closedPoints s U
  intro x hx
  have hp := hU (pointOfClosedPoint s x hx) (pointOfClosedPoint_comp s x hx)
  have hm := hp ⟨IsLocalRing.closedPoint K, rfl⟩
  change pointOfClosedPoint s x hx (IsLocalRing.closedPoint K) ∈ U at hm
  rwa [pointOfClosedPoint_apply] at hm

end FLT.Mazur.AlgClosedOpenCover
