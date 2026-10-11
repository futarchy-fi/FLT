/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicFormalCotangentSpaceMap
public import FLT.Mazur.AdicPresentationScalarTowers
public import FLT.Mazur.AdicSeparatedDerivation

/-!
# Formal degree-zero maps differentiate every completed section

Separatedness and the ideal-filtration compatibility of the formal base map
extend the original tensor formula to all sections of the presenting completion.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicFormalCotangentSpaceMap

open AdicExtensionProjection

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (P : Algebra.Extension.{u} R A)
  (Q : Algebra.Extension.{u} R B) (I : Ideal A) (J : Ideal B)
  (e : AdicCompletion I A →ₐ[R] AdicCompletion J B)
  (f : AdicCompletion (ideal P I) P.Ring →ₐ[R] AdicCompletion (ideal Q J) Q.Ring)
  (hf : ∀ x, projection Q J (f x) = e (projection P I x))
  [IsNoetherianRing A] [IsNoetherianRing P.Ring] [Module.Finite A P.CotangentSpace]

/-- The formal cotangent-space map differentiates the lift on ALL completed sections. -/
theorem map_completed
    (he : (I.map (algebraMap A (AdicCompletion I A))).map e.toRingHom ≤
      J.map (algebraMap B (AdicCompletion J B)))
    (a : AdicCompletion (ideal P I) P.Ring) :
    map P Q I J e f hf (AdicPresentationDerivation.derivation P I a) =
      AdicPresentationDerivation.derivation Q J (f a) := by
  let N := AdicCompletion J Q.CotangentSpace
  let _ := AdicPresentationDerivation.spaceModule P I
  let _ := AdicPresentationDerivation.spaceModule Q J
  let _ := AdicPresentationScalarTowers.relativeTower P I
  let _ := AdicPresentationScalarTowers.targetTower Q J
  let _ : Module (AdicCompletion (ideal P I) P.Ring) N :=
    Module.compHom _ (e.toRingHom.comp (projection P I).toRingHom)
  let _ : Algebra P.Ring (AdicCompletion J B) :=
    ((e.toRingHom.comp (algebraMap A (AdicCompletion I A))).comp
      (algebraMap P.Ring A)).toAlgebra
  let _ : Module P.Ring N := Module.compHom _ (algebraMap P.Ring (AdicCompletion J B))
  let _ : IsScalarTower P.Ring (AdicCompletion J B) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : IsScalarTower P.Ring (AdicCompletion (ideal P I) P.Ring) N :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      change e (projection P I (AdicCompletion.of (ideal P I) P.Ring r)) • x = _
      rw [projection_of]
      rfl
  let _ : IsScalarTower R (AdicCompletion (ideal P I) P.Ring) N :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      change e (projection P I (algebraMap R (AdicCompletion (ideal P I) P.Ring) r)) • x = _
      rw [(projection P I).commutes, e.commutes, algebraMap_smul]
  have hI : (ideal P I).map (algebraMap P.Ring (AdicCompletion J B)) ≤
      J.map (algebraMap B (AdicCompletion J B)) := by
    change (ideal P I).map ((e.toRingHom.comp (algebraMap A (AdicCompletion I A))).comp
      (algebraMap P.Ring A)) ≤ _
    rw [← Ideal.map_map, ideal_map, ← Ideal.map_map]
    exact he
  let _ : IsHausdorff (ideal P I) N := by
    let _ : IsHausdorff (J.map (algebraMap B (AdicCompletion J B))) N :=
      (IsHausdorff.map_algebraMap_iff (S := AdicCompletion J B) (I := J)).mpr inferInstance
    exact IsHausdorff.of_map hI
  let L : AdicCompletion I P.CotangentSpace →ₗ[AdicCompletion (ideal P I) P.Ring] N :=
    { (map P Q I J e f hf).toAddHom with
      map_smul' := fun r x ↦ by
        change map P Q I J e f hf (projection P I r • x) = _
        exact (map P Q I J e f hf).map_smulₛₗ _ _ }
  let d := DerivationAlgEquivTransport.pullback f (fun r x ↦ by
    change projection Q J (f r) • x = e (projection P I r) • x
    rw [hf]) (AdicPresentationDerivation.derivation Q J)
  have hd : L.compDer (AdicPresentationDerivation.derivation P I) = d := by
    apply AdicSeparatedDerivation.ext_of (ideal P I) (ideal P I).fg_of_isNoetherianRing
    intro x
    change map P Q I J e f hf
      (AdicPresentationDerivation.derivation P I (AdicCompletion.of (ideal P I) P.Ring x)) = _
    rw [AdicPresentationDerivation.derivation_of, map_of_tmul]
    change e 1 • AdicPresentationDerivation.derivation Q J
      (f (AdicCompletion.of (ideal P I) P.Ring x)) = _
    rw [map_one, one_smul]
    rfl
  exact Derivation.congr_fun hd a

end FLT.Mazur.AdicFormalCotangentSpaceMap
