/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfSpecialFiberFreeness
public import FLT.GroupScheme.RaynaudQuotientFiberFreeness

/-!
# Relative flatness of contracted three-adic Hopf quotient coordinates

The contracted inclusion stays injective on the residue fibre. Finite
commutative Hopf-subalgebra freeness makes that fibre free, and principal
fibre lifting proves relative flatness over the three-adic integers.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

variable {X Y : FF ℤ_[3] ℚ_[3]}

/-- The special fibre of a contracted quotient inclusion is a free module
over the quotient's special fibre. -/
theorem GenericGaloisHom.quotientCoordinates_free_mod_three
    (q : GenericGaloisHom X Y) :
    Module.Free (q.quotientCoordinates ⧸ Ideal.span {(3 : q.quotientCoordinates)})
      ((q.quotientCoordinates ⧸ Ideal.span {(3 : q.quotientCoordinates)})
        ⊗[q.quotientCoordinates] X.CoordinateRing) := by
  let I : Ideal ℤ_[3] := Ideal.span {(3 : ℤ_[3])}
  let : I.IsMaximal := by
    dsimp [I]
    have hp := PadicInt.maximalIdeal_eq_span_p (p := 3)
    norm_num at hp
    rw [← hp]
    infer_instance
  have h := HopfAlgebra.free_quotientFiber_of_injective_baseChange q.quotientInclusion
    (by ext; rfl) I (q.quotientInclusion_baseChange_injective (ℤ_[3] ⧸ I))
  have hI : I.map (algebraMap ℤ_[3] q.quotientCoordinates) =
      Ideal.span {(3 : q.quotientCoordinates)} := by
    simp only [I, Ideal.map_span, Set.image_singleton]
    congr 1
    exact congrArg singleton (map_ofNat (algebraMap ℤ_[3] q.quotientCoordinates) 3)
  change Module.Free (q.quotientCoordinates ⧸ I.map (algebraMap ℤ_[3] q.quotientCoordinates))
    ((q.quotientCoordinates ⧸ I.map (algebraMap ℤ_[3] q.quotientCoordinates))
      ⊗[q.quotientCoordinates] X.CoordinateRing) at h
  rw [hI] at h
  exact h

/-- Contracted quotient coordinates of a finite flat three-adic Hopf algebra
make the original coordinate algebra relatively flat. -/
theorem GenericGaloisHom.quotientCoordinates_flat
    (q : GenericGaloisHom X Y) : Module.Flat q.quotientCoordinates X.CoordinateRing := by
  let := q.quotientCoordinates_free_mod_three
  exact q.quotientCoordinates_flat_of_free_mod_three

end ThreeAdicPlan
