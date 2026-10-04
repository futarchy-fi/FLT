/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.FiniteUniformizerRootCharacter
public import FLT.AbsoluteGaloisGroup.TameRootIntegers

/-!
# The finite Galois model of the rational tame character

The fixing subgroup of the chosen-root field is open and normal. Its finite
DVR has a proved uniformizer mapping to the exact tame root. The finite
uniformizer character therefore computes the specified absolute character.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NumberField IsLocalRing IntermediateField LocalRamification GaloisRepresentation.Extensions
namespace LocalRoot
variable (p : ℕ) [Fact p.Prime]
local notation "v" => LocalCyclotomic.rationalPlace p
local notation "F" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
local notation "Ω" => AlgebraicClosure F

/-- The finite Galois level cut out by the actual tame-root field. -/
def rationalTameRootLevel : OpenNormalSubgroup (Field.absoluteGaloisGroup F) := by
  let := rationalTameRootField_isGalois p
  exact
    { toSubgroup := (tameRootField v).fixingSubgroup
      isOpen' := (InfiniteGalois.isOpen_iff_finite _).mpr inferInstance
      isNormal' := (InfiniteGalois.normal_iff_isGalois _).mpr inferInstance }

/-- The constructed finite Galois level is exactly the chosen-root field. -/
theorem rationalTameRootLevel_fixedField :
    fixedField (rationalTameRootLevel p).toSubgroup = tameRootField v :=
  InfiniteGalois.fixedField_fixingSubgroup _

local notation "N" => rationalTameRootLevel p
local notation "L" => fixedField
  (OpenSubgroup.toSubgroup (OpenNormalSubgroup.toOpenSubgroup (rationalTameRootLevel p)))
local notation "D" => IntegralClosure O L
attribute [local instance] finiteLevel_finiteDimensional finiteLevel_isDVR
  finiteLevel_residue_finite

/-- A uniformizer in the actual finite level maps to the exact chosen tame root. -/
theorem rationalTameRootLevel_uniformizer :
    ∃ π : D, Irreducible π ∧ (π.1 : Ω) = tameUniformizerRoot v := by
  rw [rationalTameRootLevel_fixedField]
  exact ⟨tameRootInteger v, (tameRootInteger_uniformizer v).1, rfl⟩

/-- The finite integral embedding intertwines restriction with the absolute Galois action. -/
theorem rationalTameRootLevel_equivariant (σ : Field.absoluteGaloisGroup F) (x : D) :
    finiteClosureToAbsolute v N ((AlgEquiv.restrictNormalHom L σ) • x) =
      σ • finiteClosureToAbsolute v N x := by
  apply Subtype.ext
  exact AlgEquiv.restrictNormal_commutes σ L x.1

set_option maxHeartbeats 1000000 in
-- The finite inertia and integral-closure towers need additional elaboration time.
set_option synthInstance.maxHeartbeats 100000 in
/-- The finite model computes tameCharacter, without an assumed root or character formula. -/
theorem rationalTameRootLevel_character :
    ∃ (π : D) (hπ : Irreducible π), (π.1 : Ω) = tameUniformizerRoot v ∧
      ∀ σ : localInertiaGroup v,
        ResidueField.map (finiteClosureToAbsolute v N)
          (ThreeAdicPlan.uniformizerCharacter hπ (finiteIdealInertiaRestriction v N σ) :
            ResidueField D) = residueFieldMap v (tameCharacter v σ : ResidueField O) := by
  obtain ⟨π, hπ, he⟩ := rationalTameRootLevel_uniformizer p
  refine ⟨π, hπ, he, fun σ ↦ ?_⟩
  exact finiteUniformizer_tameCharacter v N hπ (tameUniformizer_spec v)
    (by rw [he]; exact tameUniformizerRoot_spec v) σ

end LocalRoot
