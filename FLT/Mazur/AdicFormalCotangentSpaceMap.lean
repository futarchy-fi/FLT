/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCotangentSpaceLift
public import FLT.Mazur.AdicPresentationDerivation
public import FLT.Mazur.DerivationAlgEquivTransport

/-!
# Formal lifts act on completed original cotangent spaces

A map of completed presenting rings over a formal target-algebra map
induces a semilinear map between completions of the ORIGINAL degree-zero
spaces. The construction uses original tensor differentials throughout.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicFormalCotangentSpaceMap

open AdicExtensionProjection
open scoped TensorProduct

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (P : Algebra.Extension.{u} R A)
  (Q : Algebra.Extension.{u} R B) (I : Ideal A) (J : Ideal B)
  (e : AdicCompletion I A →ₐ[R] AdicCompletion J B)
  (f : AdicCompletion (ideal P I) P.Ring →ₐ[R] AdicCompletion (ideal Q J) Q.Ring)
  (hf : ∀ x, projection Q J (f x) = e (projection P I x))

/-- Differentiate the image of each original presenting section. -/
def originalDerivation :
    let _ : Module P.Ring (AdicCompletion J Q.CotangentSpace) := Module.compHom _
      ((e.toRingHom.comp (algebraMap A (AdicCompletion I A))).comp (algebraMap P.Ring A))
    Derivation R P.Ring (AdicCompletion J Q.CotangentSpace) := by
  let _ : Module P.Ring (AdicCompletion J Q.CotangentSpace) := Module.compHom _
    ((e.toRingHom.comp (algebraMap A (AdicCompletion I A))).comp (algebraMap P.Ring A))
  let _ := AdicPresentationDerivation.spaceModule Q J
  exact DerivationAlgEquivTransport.pullback
    (f.comp (IsScalarTower.toAlgHom R P.Ring (AdicCompletion (ideal P I) P.Ring)))
    (fun a x ↦ by
      change projection Q J (f (AdicCompletion.of (ideal P I) P.Ring a)) • x =
        e (AdicCompletion.of I A (algebraMap P.Ring A a)) • x
      rw [hf, projection_of]) (AdicPresentationDerivation.derivation Q J)

variable [IsNoetherianRing A] [Module.Finite A P.CotangentSpace]

/-- A genuine formal presentation map acts on completed original degree-zero spaces. -/
def map : AdicCompletion I P.CotangentSpace →ₛₗ[e.toRingHom]
    AdicCompletion J Q.CotangentSpace := by
  let N := AdicCompletion J Q.CotangentSpace
  let _ : IsScalarTower R (AdicCompletion J B) N :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      rw [IsScalarTower.algebraMap_eq R B (AdicCompletion J B)]
      change algebraMap B (AdicCompletion J B) (algebraMap R B r) • x = r • x
      rw [algebraMap_smul, algebraMap_smul]
  let _ : Module (AdicCompletion I A) N := Module.compHom _ e.toRingHom
  let _ : Module A N := Module.compHom _ (algebraMap A (AdicCompletion I A))
  let _ : Module P.Ring N := Module.compHom _ (algebraMap P.Ring A)
  let _ : IsScalarTower A (AdicCompletion I A) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : IsScalarTower P.Ring A N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : IsScalarTower R P.Ring N :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      change e (algebraMap A (AdicCompletion I A)
        (algebraMap P.Ring A (algebraMap R P.Ring r))) • x = r • x
      rw [← IsScalarTower.algebraMap_apply R P.Ring A,
        ← IsScalarTower.algebraMap_apply R A (AdicCompletion I A), e.commutes,
        algebraMap_smul]
  let g := AdicCotangentSpaceLift.lift P I (originalDerivation P Q I J e f hf)
  exact { g.toAddHom with map_smul' := fun a x ↦ g.map_smul a x }

/-- On original tensor differentials the map differentiates the actual formal lift. -/
theorem map_of_tmul (a : A) (x : P.Ring) :
    map P Q I J e f hf (AdicCompletion.of I P.CotangentSpace
      (a ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x)) =
        e (AdicCompletion.of I A a) • AdicPresentationDerivation.derivation Q J
          (f (AdicCompletion.of (ideal P I) P.Ring x)) := by
  let N := AdicCompletion J Q.CotangentSpace
  let _ : IsScalarTower R (AdicCompletion J B) N :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      rw [IsScalarTower.algebraMap_eq R B (AdicCompletion J B)]
      change algebraMap B (AdicCompletion J B) (algebraMap R B r) • x = r • x
      rw [algebraMap_smul, algebraMap_smul]
  let _ : Module (AdicCompletion I A) N := Module.compHom _ e.toRingHom
  let _ : Module A N := Module.compHom _ (algebraMap A (AdicCompletion I A))
  let _ : Module P.Ring N := Module.compHom _ (algebraMap P.Ring A)
  let _ : IsScalarTower A (AdicCompletion I A) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : IsScalarTower P.Ring A N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : IsScalarTower R P.Ring N :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      change e (algebraMap A (AdicCompletion I A)
        (algebraMap P.Ring A (algebraMap R P.Ring r))) • x = r • x
      rw [← IsScalarTower.algebraMap_apply R P.Ring A,
        ← IsScalarTower.algebraMap_apply R A (AdicCompletion I A), e.commutes,
        algebraMap_smul]
  exact AdicCotangentSpaceLift.lift_of_tmul P I (originalDerivation P Q I J e f hf) a x

end FLT.Mazur.AdicFormalCotangentSpaceMap
