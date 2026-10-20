/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCharacterStructure
public import FLT.Mazur.FiniteCharacterAdicSurjectivity

/-!
# The effective chart coordinates as an algebra map over the original base

The proved structure equation supplies scalar compatibility. Nakayama then
lifts surjectivity of the initial full coordinate map to the complete base.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart CharacterSchemeBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R G : Type} [CommRing R] [AddCommGroup G] [Finite G]
  (I : Ideal R) [IsAdicComplete I R] (t : R) (ht : t ∈ I)
  (g : stageSource I G 0 ⟶ stageGroup I t 0)

/-- The effective coordinates retain the algebra structure of the original complete ring. -/
def effectiveCoordinates : Coordinate (equation t) 1 →ₐ[R] AddMonoidAlgebra R G :=
  { FiniteCharacterAdicHom.liftHom I (towerCoordinates I t ht g)
      (towerCoordinates_reduction I t ht g) with
    commutes' := by
      intro a
      have h := effectiveAffine_structure I t ht g
      change Spec.map _ ≫ Spec.map _ = Spec.map _ at h
      rw [← Spec.map_comp] at h
      exact RingHom.congr_fun (congrArg (fun k => k.hom) (Spec.map_injective h)) a }

/-- Taking spectra recovers exactly the constructed effective affine morphism. -/
theorem effectiveCoordinates_spec :
    Spec.map (CommRingCat.ofHom (effectiveCoordinates I t ht g).toRingHom) =
      effectiveAffine I t ht g := rfl

/-- All positive-order full coordinate reductions are the prescribed tower maps. -/
theorem effectiveCoordinates_reduction (m : ℕ) :
    (FiniteCharacterAdicElements.reduction I m).comp
      (effectiveCoordinates I t ht g).toRingHom = towerCoordinates I t ht g m :=
  FiniteCharacterAdicHom.reduction_liftHom I (towerCoordinates I t ht g)
    (towerCoordinates_reduction I t ht g) m

/-- Initial full coordinate surjectivity lifts to the original complete-base chart map. -/
theorem effectiveCoordinates_surjective
    (hg : Function.Surjective (towerCoordinates I t ht g 0)) :
    Function.Surjective (effectiveCoordinates I t ht g) := by
  apply FiniteCharacterAdicElements.surjective_of_initial_reduction I
  have h : Function.Surjective ((FiniteCharacterAdicElements.reduction I 0).comp
      (effectiveCoordinates I t ht g).toRingHom) := by
    rw [effectiveCoordinates_reduction]
    exact hg
  exact (congrArg (fun J : Ideal R => Function.Surjective
    ((DiagonalizableCobar.coefficientReduction R G J).comp
      (effectiveCoordinates I t ht g))) (pow_one I)).mp h

end FLT.Mazur.OneGonAdicCharacterTower
