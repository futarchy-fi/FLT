/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFlatFppfTargetDensity
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Constructing principal fppf neighborhoods inside prescribed target opens

Flatness and dominance refine every nonempty affine-target open to an actual
nonempty principal open with a whole-source fppf projection. The coefficient
is nonnilpotent; no reducedness or generic flatness is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeFppfTargetOpen
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
  [Flat f] [IsDominant f] [IsAffine Y]

/-- Construct an actual principal fppf neighborhood within any nonempty original target open. -/
theorem exists_principal_fppf_of_nonempty (U : Y.Opens) (hU : (U : Set Y).Nonempty) :
    ∃ r : Γ(Y, ⊤), ¬ IsNilpotent r ∧ Y.basicOpen r ≤ U ∧
      Flat (pullback.snd f (Y.basicOpen r).ι) ∧
      Surjective (pullback.snd f (Y.basicOpen r).ι) := by
  obtain ⟨x, hxU, hx⟩ := (dense_of_flat f).inter_open_nonempty U U.isOpen hU
  obtain ⟨r, hr, hxr⟩ :=
    (isAffineOpen_top Y).exists_basicOpen_le (⟨x, hxU, hx⟩ : ↥(U ⊓ locus f)) (by trivial)
  refine ⟨r, ?_, hr.trans inf_le_left, inferInstance,
    surjective_of_le f (Y.basicOpen r) (hr.trans inf_le_right)⟩
  intro hn
  rw [(Scheme.isNilpotent_iff_basicOpen_eq_bot r).mp hn] at hxr
  exact hxr

/-- A nonnilpotent original function refines to a nonnilpotent principal fppf coefficient. -/
theorem exists_principal_fppf_of_coefficient (r : Γ(Y, ⊤)) (hr : ¬ IsNilpotent r) :
    ∃ s : Γ(Y, ⊤), ¬ IsNilpotent s ∧ Y.basicOpen s ≤ Y.basicOpen r ∧
      Flat (pullback.snd f (Y.basicOpen s).ι) ∧
      Surjective (pullback.snd f (Y.basicOpen s).ι) := by
  apply exists_principal_fppf_of_nonempty f
  apply (Y.basicOpen r).ne_bot_iff_nonempty.mp
  exact fun h ↦ hr ((Scheme.isNilpotent_iff_basicOpen_eq_bot r).mpr h)

end FLT.Mazur.SchemeFppfTargetOpen
