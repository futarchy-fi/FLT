/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective

/-!
# Finite-group cohomology in characteristic zero

Maschke's theorem makes the group algebra semisimple. Its modules are
projective, so the Ext presentation of group cohomology vanishes in positive
degrees. This uses the proved averaging theorem, with no homotopy hypothesis.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open CategoryTheory Limits

variable (k G : Type u) [Field k] [CharZero k] [Group G] [Finite G]

/-- A finite-group representation over a characteristic-zero field is projective. -/
theorem finiteCharacteristicZero_projective (A : Rep k G) : Projective A := by
  let : NeZero (Nat.card G : k) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  let : Module.Projective (MonoidAlgebra k G) (Rep.toModuleMonoidAlgebra.obj A) :=
    Module.projective_of_isSemisimpleRing _ _
  apply (Rep.equivalenceModuleMonoidAlgebra.map_projective_iff A).mp
  change Projective (Rep.toModuleMonoidAlgebra.obj A)
  exact ModuleCat.projective_of_categoryTheory_projective _

/-- Positive finite-group cohomology vanishes over a characteristic-zero field. -/
theorem finiteCharacteristicZero_cohomology_isZero (A : Rep k G) (n : ℕ) :
    IsZero (groupCohomology A (n + 1)) := by
  let : Projective (Rep.trivial k G k) := finiteCharacteristicZero_projective k G _
  exact (isZero_Ext_succ_of_projective (Rep.trivial k G k) A n).of_iso
    (groupCohomologyIsoExt A (n + 1))

end LocalClassFieldTheory
