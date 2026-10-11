/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import FLT.Mazur.QuotientRelativeDerivation

/-!
# Original differentials descend through the relation square

The universal derivation with values in the original presentation cotangent
space kills the square of the relation ideal. It therefore descends through
infinitesimalization without replacing the original differential module.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.InfinitesimalCotangentDerivation

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (P : Algebra.Extension R A)

/-- The original differential after tensoring with the target algebra. -/
def derivation : Derivation R P.Ring P.CotangentSpace :=
  ((TensorProduct.mk P.Ring A Ω[P.Ring⁄R] 1).restrictScalars P.Ring).compDer
    (KaehlerDifferential.D R P.Ring)

/-- The original differential has its expected tensor representative. -/
@[simp] theorem derivation_apply (x : P.Ring) :
    derivation P x = 1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x := rfl

/-- Relations act trivially on the original cotangent space. -/
theorem ker_smul (x : P.ker) (m : P.CotangentSpace) : (x : P.Ring) • m = 0 := by
  rw [← algebraMap_smul A (x : P.Ring) m, x.property, zero_smul]

/-- Products of relations introduce no differential relation after tensoring with the target. -/
theorem derivation_square (x : P.Ring) (hx : x ∈ P.ker ^ 2) : derivation P x = 0 := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_) (fun a b ha hb ↦ ?_)
  · rw [(derivation P).leibniz, ker_smul P ⟨a, ha⟩, ker_smul P ⟨b, hb⟩, add_zero]
  · rw [map_add, ha, hb, add_zero]

/-- Infinitesimal coefficients act through the original target algebra. -/
local instance spaceModule : Module (P.Ring ⧸ P.ker ^ 2) P.CotangentSpace :=
  Module.compHom P.CotangentSpace (algebraMap P.infinitesimal.Ring A)

/-- The quotient action agrees with the original presenting-ring action. -/
local instance spaceTower : IsScalarTower P.Ring (P.Ring ⧸ P.ker ^ 2) P.CotangentSpace :=
  IsScalarTower.of_algebraMap_smul fun r m ↦ by
    change algebraMap P.Ring A r • m = _
    exact algebraMap_smul A r m

/-- The descended derivation still takes values in the original cotangent space. -/
def descended : Derivation R P.infinitesimal.Ring P.CotangentSpace :=
  @QuotientRelativeDerivation.lift R P.Ring P.CotangentSpace _ _ _ (P.ker ^ 2)
    _ _ _ (spaceModule P) (spaceTower P) (derivation P) (derivation_square P)

/-- Infinitesimalization retains every original differential value. -/
theorem descended_mk (x : P.Ring) :
    descended P (P.toInfinitesimal.toAlgHom x) =
      1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x := rfl

end FLT.Mazur.InfinitesimalCotangentDerivation
