/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.IntegralClosedImmersion

/-!
# Equations of an actual closed inclusion

The closure comparison is an isomorphism. Its injectivity identifies the
kernel of the prescribed coordinate map with the generic closure ideal.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]

/-- Closed inclusions have exactly the equations of their generic closure. -/
theorem ModelHom.ker_eq_closureIdeal {X Y : FF R K} (f : ModelHom X Y)
    (hi : Function.Injective (genericHom f)) (hf : Function.Surjective f) :
    RingHom.ker f.toAlgHom.toRingHom = (genericHom f).closureIdeal := by
  ext a
  change f a = 0 ↔ a ∈ (genericHom f).closureIdeal
  have he : f a = f.closureIso hi hf
      (Ideal.Quotient.mk (genericHom f).closureIdeal a) := rfl
  rw [he, ← map_zero (f.closureIso hi hf)]
  exact (f.closureIso hi hf).injective.eq_iff.trans Ideal.Quotient.eq_zero_iff_mem

end ThreeAdicPlan
