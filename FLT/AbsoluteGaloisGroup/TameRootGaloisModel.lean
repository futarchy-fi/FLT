/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.CompletionIntegersAdic
public import FLT.AbsoluteGaloisGroup.FiniteUniformizerRootCharacter
public import FLT.AbsoluteGaloisGroup.TameRootIntegers

/-!
# The tame-root Galois model at every finite number-field place

Henselianity supplies the roots of unity in the local base. The chosen-root
field is therefore Galois, and its actual finite uniformizer character
computes the specified absolute tame character.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NumberField IsLocalRing IntermediateField LocalRamification GaloisRepresentation.Extensions
namespace LocalRoot
variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ω" => AlgebraicClosure F

/-- Normality of the specified tame-root field at every finite number-field place. -/
theorem tameRootField_isGalois : IsGalois F (tameRootField v) := by
  obtain ⟨ζ, hζ⟩ := completion_exists_primitive_tame_root v
  let := tameRootField_normal_of_primitive v hζ
  exact ⟨⟩

/-- The finite Galois level cut out by the actual tame-root field. -/
def tameRootLevel : OpenNormalSubgroup (Field.absoluteGaloisGroup F) := by
  let := tameRootField_isGalois v
  exact
    { toSubgroup := (tameRootField v).fixingSubgroup
      isOpen' := (InfiniteGalois.isOpen_iff_finite _).mpr inferInstance
      isNormal' := (InfiniteGalois.normal_iff_isGalois _).mpr inferInstance }

/-- The constructed finite Galois level is exactly the chosen-root field. -/
theorem tameRootLevel_fixedField :
    fixedField (tameRootLevel v).toSubgroup = tameRootField v :=
  InfiniteGalois.fixedField_fixingSubgroup _

local notation "N" => tameRootLevel v
local notation "L" => fixedField
  (OpenSubgroup.toSubgroup (OpenNormalSubgroup.toOpenSubgroup (tameRootLevel v)))
local notation "D" => IntegralClosure O L
attribute [local instance] finiteLevel_finiteDimensional finiteLevel_isDVR
  finiteLevel_residue_finite

/-- A uniformizer in the actual finite level maps to the exact chosen tame root. -/
theorem tameRootLevel_uniformizer :
    ∃ π : D, Irreducible π ∧ (π.1 : Ω) = tameUniformizerRoot v := by
  rw [tameRootLevel_fixedField]
  exact ⟨tameRootInteger v, (tameRootInteger_uniformizer v).1, rfl⟩

/-- The finite integral embedding intertwines restriction with the absolute Galois action. -/
theorem tameRootLevel_equivariant (σ : Field.absoluteGaloisGroup F) (x : D) :
    finiteClosureToAbsolute v N ((AlgEquiv.restrictNormalHom L σ) • x) =
      σ • finiteClosureToAbsolute v N x := by
  apply Subtype.ext
  exact AlgEquiv.restrictNormal_commutes σ L x.1

set_option maxHeartbeats 1000000 in
-- The finite inertia and integral-closure towers need additional elaboration time.
set_option synthInstance.maxHeartbeats 100000 in
/-- The finite model computes tameCharacter, without an assumed root or character formula. -/
theorem tameRootLevel_character :
    ∃ (π : D) (hπ : Irreducible π), (π.1 : Ω) = tameUniformizerRoot v ∧
      ∀ σ : localInertiaGroup v,
        ResidueField.map (finiteClosureToAbsolute v N)
          (ThreeAdicPlan.uniformizerCharacter hπ (finiteIdealInertiaRestriction v N σ) :
            ResidueField D) = residueFieldMap v (tameCharacter v σ : ResidueField O) := by
  obtain ⟨π, hπ, he⟩ := tameRootLevel_uniformizer v
  refine ⟨π, hπ, he, fun σ ↦ ?_⟩
  exact finiteUniformizer_tameCharacter v N hπ (tameUniformizer_spec v)
    (by rw [he]; exact tameUniformizerRoot_spec v) σ

end LocalRoot
