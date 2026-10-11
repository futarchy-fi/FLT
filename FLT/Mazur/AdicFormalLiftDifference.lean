/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicSquareZeroFormalConormal
public import FLT.Mazur.AdicFiniteModuleLift

/-!
# Explicit differences of formal presentation lifts

Restrict two formal lifts to original sections and take their actual
conormal difference. Finite-module completion extends this difference to
the completed ORIGINAL degree-zero space.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicFormalLiftDifference

open AdicExtensionProjection AdicFormalPresentationHom Algebra.Extension
open scoped TensorProduct

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (P : Algebra.Extension.{u} R A)
  (Q : Algebra.Extension.{u} R B) (I : Ideal A) (J : Ideal B)
  (e : AdicCompletion I A →ₐ[R] AdicCompletion J B)
  (f g : AdicCompletion (ideal P I) P.Ring →ₐ[R] AdicCompletion (ideal Q J) Q.Ring)
  (hf : ∀ x, projection Q J (f x) = e (projection P I x))
  (hg : ∀ x, projection Q J (g x) = e (projection P I x))

/-- Restrict a genuine formal lift to the original presenting ring. -/
def originalHom : let _ := (sourceScalars I J e).toAlgebra; P.Hom (completed Q J) := by
  let _ := (sourceScalars I J e).toAlgebra
  exact
    { toRingHom := (f.comp
        (IsScalarTower.toAlgHom R P.Ring (AdicCompletion (ideal P I) P.Ring))).toRingHom
      toRingHom_algebraMap := (f.comp
        (IsScalarTower.toAlgHom R P.Ring (AdicCompletion (ideal P I) P.Ring))).commutes
      algebraMap_toRingHom := fun x ↦ by
        change projection Q J (f (AdicCompletion.of (ideal P I) P.Ring x)) = _
        rw [hf, projection_of]
        rfl }

/-- The difference retains the actual subtraction of the two formal section images. -/
def difference (x : P.Ring) : (completed Q J).ker :=
  ⟨f (AdicCompletion.of (ideal P I) P.Ring x) -
      g (AdicCompletion.of (ideal P I) P.Ring x), by
    change projection Q J (_ - _) = 0
    rw [map_sub, hf, hg, sub_self]⟩

variable [IsNoetherianRing A] [Module.Finite A P.CotangentSpace]

/-- Extend the explicit original difference to the completed original cotangent space. -/
def formalHomotopy : AdicCompletion I P.CotangentSpace →ₛₗ[e.toRingHom]
    (completed Q J).Cotangent := by
  let _ := (sourceScalars I J e).toAlgebra
  let _ : Module (AdicCompletion I A) (completed Q J).Cotangent :=
    Module.compHom _ e.toRingHom
  let _ : IsScalarTower A (AdicCompletion I A) (completed Q J).Cotangent :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let h := AdicFiniteModuleLift.lift I
    ((originalHom P Q I J e f hf).sub (originalHom P Q I J e g hg))
  exact { h.toAddHom with map_smul' := fun a x ↦ h.map_smul a x }

/-- Original tensor differentials map to the conormal class of the explicit lift difference. -/
theorem formalHomotopy_of_tmul (a : A) (x : P.Ring) :
    formalHomotopy P Q I J e f g hf hg (AdicCompletion.of I P.CotangentSpace
      (a ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x)) =
        e (AdicCompletion.of I A a) • Cotangent.mk (difference P Q I J e f g hf hg x) := by
  let _ := (sourceScalars I J e).toAlgebra
  let _ : Module (AdicCompletion I A) (completed Q J).Cotangent :=
    Module.compHom _ e.toRingHom
  let _ : IsScalarTower A (AdicCompletion I A) (completed Q J).Cotangent :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  change AdicFiniteModuleLift.lift I
    ((originalHom P Q I J e f hf).sub (originalHom P Q I J e g hg)) _ = _
  rw [AdicFiniteModuleLift.lift_of, Hom.sub_tmul]
  rfl

end FLT.Mazur.AdicFormalLiftDifference
