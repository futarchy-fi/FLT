/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatCotangent

/-! # Actual representatives for kernels of closed cotangent maps -/

@[expose] public noncomputable section
namespace ThreeAdicPlan
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

/-- A closed model map carries the original augmentation ideal onto the target ideal. -/
theorem ModelHom.cotangentIdeal_map {X Y : FF R K} (f : ModelHom X Y)
    (hf : Function.Surjective f) : Y.cotangentIdeal.map f.toAlgHom = X.cotangentIdeal := by
  apply le_antisymm
  · exact Ideal.map_le_iff_le_comap.mpr f.cotangentIdeal_le
  · intro a ha
    obtain ⟨b, rfl⟩ := hf a
    apply Ideal.mem_map_of_mem
    change Coalgebra.counit (R := R) b = 0
    exact (CoalgHomClass.counit_comp_apply f b).symm.trans ha

/-- A cotangent class killed by a closed map has an actual coordinate-kernel representative. -/
theorem ModelHom.cotangentMap_eq_zero_iff {X Y : FF R K} (f : ModelHom X Y)
    (hf : Function.Surjective f) (x : Y.Cotangent) :
    f.cotangentMap x = 0 ↔
      ∃ a : Y.cotangentIdeal, f a = 0 ∧ Y.cotangentIdeal.toCotangent a = x := by
  constructor
  · intro hx
    obtain ⟨b, rfl⟩ := Y.cotangentIdeal.toCotangent_surjective x
    have hb : f (b : Y.CoordinateRing) ∈ X.cotangentIdeal ^ 2 :=
      (Ideal.toCotangent_eq_zero _ _).mp hx
    rw [← f.cotangentIdeal_map hf, ← Ideal.map_pow] at hb
    have hc := Ideal.comap_map_of_surjective f.toAlgHom.toRingHom hf
      (Y.cotangentIdeal ^ 2)
    have hb' : (b : Y.CoordinateRing) ∈
        Y.cotangentIdeal ^ 2 ⊔ RingHom.ker f.toAlgHom := by
      change (b : Y.CoordinateRing) ∈
        Y.cotangentIdeal ^ 2 ⊔ Ideal.comap f.toAlgHom.toRingHom ⊥
      rw [← hc]
      exact hb
    obtain ⟨c, hc, a, ha, he⟩ := Submodule.mem_sup.mp hb'
    have ha' : a ∈ Y.cotangentIdeal := by
      have hc' := Ideal.pow_le_self (I := Y.cotangentIdeal) two_ne_zero hc
      exact (Y.cotangentIdeal.add_mem_iff_right hc').mp (he ▸ b.property)
    refine ⟨⟨a, ha'⟩, ha, ?_⟩
    apply (Ideal.toCotangent_eq _).mpr
    change a - (b : Y.CoordinateRing) ∈ Y.cotangentIdeal ^ 2
    have he' : a - (b : Y.CoordinateRing) = -c := by rw [← he]; abel
    rw [he']
    exact (Y.cotangentIdeal ^ 2).neg_mem hc
  · rintro ⟨a, ha, rfl⟩
    rw [ModelHom.cotangentMap_mk]
    convert X.cotangentIdeal.toCotangent.map_zero using 1
    exact congrArg X.cotangentIdeal.toCotangent (Subtype.ext ha)

end ThreeAdicPlan
