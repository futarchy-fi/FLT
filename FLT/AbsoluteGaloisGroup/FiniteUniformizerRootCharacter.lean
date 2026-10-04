/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.FiniteCharacterInertia
public import FLT.AbsoluteGaloisGroup.TameCharacterSurjective

/-!
# Finite uniformizers and the absolute reduced root character

The residue comparison map is induced by the actual finite-field inclusion.
When a finite uniformizer is a root of a base element, its character is the
absolute reduced root character under that map. No character-evaluation
identity is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open NumberField IsLocalRing
namespace LocalRamification
variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ω" => AlgebraicClosure Kv
local notation "A" => IntegralClosure O Ω
variable (N : OpenNormalSubgroup (Field.absoluteGaloisGroup (v.adicCompletion K)))
local notation "L" => IntermediateField.fixedField N.toSubgroup
local notation "D" => IntegralClosure O L
attribute [local instance] finiteLevel_finiteDimensional finiteLevel_isDVR
  finiteLevel_residue_finite

/-- The actual integral-closure inclusion associated to the finite Galois field. -/
def finiteClosureToAbsolute : D →+* A :=
  IntegralClosure.map ((L).val.restrictScalars O)

/-- The inclusion is local, so its residue map is defined canonically. -/
instance finiteClosureToAbsolute_isLocalHom : IsLocalHom (finiteClosureToAbsolute v N) := by
  have hi : ((finiteClosureToAbsolute v N).comp (algebraMap O D)).IsIntegral := by
    change (algebraMap O A).IsIntegral
    exact algebraMap_isIntegral_iff.mpr inferInstance
  exact (RingHom.IsIntegral.tower_top _ _ hi).isLocalHom
    (IntegralClosure.map_injective _ ((L).val.restrictScalars O).injective)

/-- The finite uniformizer ratio agrees with the actual integral absolute root ratio. -/
theorem finiteUniformizer_integralRatio {π : D} (hπ : Irreducible π)
    {n : ℕ} (hn : 0 < n) {a : Kv} (ha : a ≠ 0)
    (hroot : (π.1 : Ω) ^ n = algebraMap Kv Ω a) (σ : localInertiaGroup v) :
    finiteClosureToAbsolute v N
      (ThreeAdicPlan.uniformizerRatio hπ (finiteIdealInertiaRestriction v N σ).val : D) =
        LocalRoot.integralRatio v hn ha hroot σ := by
  apply Subtype.ext
  change _ = σ.val (π.1 : Ω) / (π.1 : Ω)
  apply (eq_div_iff (LocalRoot.root_ne_zero v hn ha hroot)).mpr
  have h := congrArg (fun x : D ↦ (finiteClosureToAbsolute v N x).1)
    (ThreeAdicPlan.uniformizer_mul_ratio hπ (finiteIdealInertiaRestriction v N σ).val)
  rw [map_mul] at h
  change (π.1 : Ω) * _ = ((σ.val.restrictNormal L) π.1 : Ω) at h
  rw [AlgEquiv.restrictNormal_apply] at h
  simpa only [mul_comm] using h

/-- The finite-DVR and absolute root characters agree after the constructed residue inclusion. -/
theorem finiteUniformizer_character {π : D} (hπ : Irreducible π)
    {n : ℕ} (hn : 0 < n) {a : Kv} (ha : a ≠ 0)
    (hroot : (π.1 : Ω) ^ n = algebraMap Kv Ω a) (σ : localInertiaGroup v) :
    ResidueField.map (finiteClosureToAbsolute v N)
      (ThreeAdicPlan.uniformizerCharacter hπ (finiteIdealInertiaRestriction v N σ) :
        ResidueField D) = (LocalRoot.character v hn ha hroot σ : ResidueField A) := by
  change residue A (finiteClosureToAbsolute v N
    (ThreeAdicPlan.uniformizerRatio hπ (finiteIdealInertiaRestriction v N σ).val : D)) = _
  rw [finiteUniformizer_integralRatio v N hπ hn ha hroot]
  rfl

/-- At a level-one root uniformizer, the finite-DVR character is the specified tame character. -/
theorem finiteUniformizer_tameCharacter {π : D} (hπ : Irreducible π)
    {a : O} (ha : Valued.v a.1 = Multiplicative.ofAdd (-1 : ℤ))
    (hroot : (π.1 : Ω) ^ (Nat.card (ResidueField O) - 1) = algebraMap Kv Ω a.1)
    (σ : localInertiaGroup v) :
    ResidueField.map (finiteClosureToAbsolute v N)
      (ThreeAdicPlan.uniformizerCharacter hπ (finiteIdealInertiaRestriction v N σ) :
        ResidueField D) = residueFieldMap v (tameCharacter v σ : ResidueField O) := by
  rw [finiteUniformizer_character v N hπ (tameDegree_pos v)
    (fun h ↦ IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero
      ha (Subtype.ext h)) hroot]
  exact (tameCharacter_residue_eq_rootCharacter v ha hroot σ).symm

end LocalRamification
