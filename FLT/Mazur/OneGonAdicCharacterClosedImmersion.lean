/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCharacterCoordinates
public import FLT.Mazur.OneGonAdicCharacterInitialEmbedding
public import FLT.Mazur.OneGonAdicCharacterGroupEffectivity
public import FLT.Mazur.WeierstrassIntegralSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The effective original character homomorphism is a closed immersion

An original initial closed embedding gives surjective complete-base chart
coordinates. The smooth map is a monomorphism, and its finite source and
separated target make it finite, hence a closed immersion into the full group.
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
  [IsClosedImmersion g.hom.hom.hom.left]

/-- The actual effective affine chart map is a closed immersion over the original ring. -/
instance effectiveAffine_isClosedImmersion : IsClosedImmersion (effectiveAffine I t ht g) := by
  rw [← effectiveCoordinates_spec]
  exact IsClosedImmersion.spec_of_surjective _
    (effectiveCoordinates_surjective I t ht g (towerCoordinates_zero_surjective I t ht g))

/-- The effective smooth map is a monomorphism into the entire original smooth group. -/
instance effectiveSmooth_mono : Mono (effectiveSmooth I t ht g) := by
  have h := effectiveSmooth_inclusion I t ht g
  let _ : Mono (effectiveSmooth I t ht g ≫ (integralSmoothOpen (equation t)).ι) := by
    rw [h]
    infer_instance
  exact mono_of_mono (effectiveSmooth I t ht g) (integralSmoothOpen (equation t)).ι

/-- The whole smooth target retains the original separated structure morphism. -/
theorem integralSmoothStructure_separated : IsSeparated (integralSmoothStructure (equation t)) := by
  unfold integralSmoothStructure
  infer_instance

omit [IsClosedImmersion g.hom.hom.hom.left] in
/-- Finiteness is retained over the original complete coefficient spectrum. -/
theorem effectiveSmooth_isFinite : IsFinite (effectiveSmooth I t ht g) := by
  let _ : Module.Finite R (AddMonoidAlgebra R G) :=
    Module.Finite.of_basis (AddMonoidAlgebra.basis G R)
  let _ : IsFinite (model R G).hom := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  let _ := integralSmoothStructure_separated t
  let _ : IsFinite (effectiveSmooth I t ht g ≫ integralSmoothStructure (equation t)) := by
    rw [effectiveSmooth_structure]
    infer_instance
  exact IsFinite.of_comp _ (integralSmoothStructure (equation t))

/-- The constructed original group homomorphism is a genuine closed subgroup embedding. -/
theorem effectiveCharacterHom_isClosedImmersion :
    IsClosedImmersion (effectiveCharacterHom I t ht g).hom.hom.hom.left := by
  change IsClosedImmersion (effectiveSmooth I t ht g)
  exact (IsClosedImmersion.iff_isFinite_and_mono _).mpr
    ⟨effectiveSmooth_isFinite I t ht g, inferInstance⟩

end FLT.Mazur.OneGonAdicCharacterTower
