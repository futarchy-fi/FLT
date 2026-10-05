/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatCotangentKernel

/-! # Cotangents are unchanged by a closed idempotent kernel -/

@[expose] public noncomputable section
namespace ThreeAdicPlan
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {X Y : FF R K}

/-- A closed map with idempotent coordinate kernel induces an isomorphism on cotangents. -/
theorem ModelHom.cotangentMap_bijective_of_idempotent_ker (f : ModelHom X Y)
    (hf : Function.Surjective f) (hk : IsIdempotentElem (RingHom.ker f.toAlgHom.toRingHom)) :
    Function.Bijective f.cotangentMap := by
  refine ⟨(injective_iff_map_eq_zero _).mpr ?_, f.cotangentMap_surjective hf⟩
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (f.cotangentMap_eq_zero_iff hf x).mp hx
  apply (Ideal.toCotangent_eq_zero _ _).mpr
  have hle : RingHom.ker f.toAlgHom.toRingHom ≤ Y.cotangentIdeal := by
    intro b hb
    change Coalgebra.counit (R := R) b = 0
    rw [← CoalgHomClass.counit_comp_apply f b, show f b = 0 from hb, map_zero]
  have hs : RingHom.ker f.toAlgHom.toRingHom ≤ Y.cotangentIdeal ^ 2 := by
    rw [pow_two, ← hk.eq]
    exact Ideal.mul_mono hle hle
  exact hs ha
end ThreeAdicPlan
