/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCharacterStages

/-!
# Coefficient maps between the actual adic stages

A map carrying the defining ideal into the new ideal induces maps at every
positive order. These retain the parameter and commute with adjacent reduction.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.OneGonAdicCharacterTower

open AdicFormallySmoothStages

variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
  (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f)

include hf in
/-- The original coefficient map carries each full ideal power into the new power. -/
theorem coefficient_pow_le (m : ℕ) : I ^ m ≤ (J ^ m).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact pow_le_pow_left' (Ideal.map_le_iff_le_comap.mpr hf) m

/-- Coefficient change on the actual positive-order quotient, without flatness assumptions. -/
def stageCoefficient (m : ℕ) : StageRing I m →+* StageRing J m :=
  Ideal.quotientMap _ f (coefficient_pow_le I J f hf (m + 1))

/-- The induced map retains the specified coefficient representatives. -/
@[simp] theorem stageCoefficient_mk (m : ℕ) (r : R) :
    stageCoefficient I J f hf m (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (f r) := rfl

/-- The actual parameter changes by the given coefficient homomorphism. -/
theorem stageCoefficient_parameter (t : R) (m : ℕ) :
    stageCoefficient I J f hf m (parameter I t m) = parameter J (f t) m := rfl

/-- Adjacent coefficient squares commute on the full quotient rings. -/
theorem stageCoefficient_restriction (m : ℕ) :
    (restriction J m).toRingHom.comp (stageCoefficient I J f hf (m + 1)) =
      (stageCoefficient I J f hf m).comp (restriction I m).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  ext r
  rfl

/-- Coefficient changes compose on the actual stages. -/
theorem stageCoefficient_comp (K : Ideal T) (g : S →+* T) (hg : J ≤ K.comap g)
    (m : ℕ) :
    (stageCoefficient J K g hg m).comp (stageCoefficient I J f hf m) =
      stageCoefficient I K (g.comp f) (fun _ hx => hg (hf hx)) m := by
  apply Ideal.Quotient.ringHom_ext
  ext r
  rfl

/-- Identity coefficient change is the identity of each original quotient. -/
theorem stageCoefficient_id (m : ℕ) :
    stageCoefficient I I (RingHom.id R) (by rfl) m = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  ext r
  rfl

end FLT.Mazur.OneGonAdicCharacterTower
