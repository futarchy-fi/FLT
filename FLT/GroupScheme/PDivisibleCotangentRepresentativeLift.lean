/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCotangentTransitions

/-! # Lifting augmentation representatives with a prescribed cotangent class -/

@[expose] public noncomputable section
namespace ThreeAdicPlan
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  {X Y : FF R K}

/-- A surjective original coordinate map maps each power of the augmentation ideal onto
that same power in the target. -/
theorem ModelHom.map_cotangentIdeal_pow (f : ModelHom X Y) (hf : Function.Surjective f)
    (r : ℕ) : (Y.cotangentIdeal ^ r).map f.toAlgHom = X.cotangentIdeal ^ r := by
  have he : Y.cotangentIdeal = X.cotangentIdeal.comap f.toAlgHom := by
    ext a
    exact (CoalgHomClass.counit_comp_apply f a).symm.congr_left
  rw [Ideal.map_pow, he]
  exact congrArg (fun I : Ideal X.CoordinateRing ↦ I ^ r)
    (Ideal.map_comap_of_surjective f.toAlgHom.toRingHom hf X.cotangentIdeal)

/-- A representative downstairs and a compatible cotangent upstairs lift simultaneously.
The correction lies in the square of the original augmentation ideal. -/
theorem ModelHom.exists_cotangent_representative_lift (f : ModelHom X Y)
    (hf : Function.Surjective f) (a : X.cotangentIdeal) (v : Y.Cotangent)
    (hv : f.cotangentMap v = X.cotangentIdeal.toCotangent a) :
    ∃ b : Y.cotangentIdeal, f b = a ∧ Y.cotangentIdeal.toCotangent b = v := by
  obtain ⟨b, hb⟩ := Y.cotangentIdeal.toCotangent_surjective v
  have hdiff : f b - a ∈ X.cotangentIdeal ^ 2 := by
    apply (Ideal.toCotangent_eq X.cotangentIdeal
      (x := ⟨f b, f.cotangentIdeal_le b.property⟩) (y := a)).mp
    change f.cotangentMap (Y.cotangentIdeal.toCotangent b) = _
    rw [hb, hv]
  rw [← f.map_cotangentIdeal_pow hf 2] at hdiff
  obtain ⟨c, hc, hfc⟩ := (Ideal.mem_map_iff_of_surjective _ hf).mp hdiff
  have hc' : c ∈ Y.cotangentIdeal := (Ideal.pow_le_self (by omega : 2 ≠ 0)) hc
  refine ⟨b - ⟨c, hc'⟩, ?_, ?_⟩
  · change f (b.val - c) = a.val
    rw [map_sub, hfc, sub_sub_cancel]
  · rw [map_sub, (Ideal.toCotangent_eq_zero _ ⟨c, hc'⟩).mpr hc, sub_zero, hb]

end ThreeAdicPlan
