/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Module filtrations for two original rings acting on a common model

Equality of the extended original ideals identifies their filtrations on
all modules over the common ring, and hence their notions of separation.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicCommonModelFiltration

variable {A B C N : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A C] [Algebra B C] [AddCommGroup N]
  [Module A N] [Module B N] [Module C N]
  [IsScalarTower A C N] [IsScalarTower B C N]
  (I : Ideal A) (J : Ideal B)
  (h : I.map (algebraMap A C) = J.map (algebraMap B C))

include h

/-- The original ideal powers give the same subsets of every common-model module. -/
theorem mem_power_iff (n : ℕ) (x : N) :
    x ∈ I ^ n • (⊤ : Submodule A N) ↔ x ∈ J ^ n • (⊤ : Submodule B N) := by
  have ha := Submodule.restrictScalars_map_smul_eq (I ^ n) (⊤ : Submodule C N)
  have hb := Submodule.restrictScalars_map_smul_eq (J ^ n) (⊤ : Submodule C N)
  rw [Submodule.restrictScalars_top] at ha hb
  rw [← ha, ← hb]
  change x ∈ (I ^ n).map (algebraMap A C) • (⊤ : Submodule C N) ↔
    x ∈ (J ^ n).map (algebraMap B C) • (⊤ : Submodule C N)
  rw [Ideal.map_pow, Ideal.map_pow, h]

/-- Separation is independent of which original ideal defines the common filtration. -/
theorem isHausdorff_iff : IsHausdorff I N ↔ IsHausdorff J N := by
  rw [← IsHausdorff.map_algebraMap_iff (S := C) (I := I),
    ← IsHausdorff.map_algebraMap_iff (S := C) (I := J), h]

end FLT.Mazur.AdicCommonModelFiltration
