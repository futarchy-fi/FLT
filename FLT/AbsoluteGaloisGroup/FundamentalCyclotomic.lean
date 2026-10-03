/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.AbsoluteGaloisGroup.FundamentalCoefficients
public import FLT.AbsoluteGaloisGroup.LocalCyclotomicTame

/-!
# The niveau-one fundamental character is cyclotomic

The comparison uses the proved normalized cyclotomic uniformizer calculation
and the action on primitive p-th roots of unity. It includes p = 2.
-/

@[expose] public section

open IsLocalRing
namespace LocalRoot

variable (p : ℕ) [Fact p.Prime]
local notation "v" => LocalCyclotomic.rationalPlace p
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "O" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "k" => ResidueField (IntegralClosure O (AlgebraicClosure Kv))

/-- The geometric residue at the rational p-adic place has characteristic p. -/
theorem rationalResidue_charP : CharP k p := by
  let : CharP (ResidueField O) p :=
    charP_of_injective_ringHom (LocalCyclotomic.residueEquiv p).symm.toRingHom.injective p
  exact residue_charP v p

attribute [local instance] rationalResidue_charP

/-- The chosen local tame root has the required niveau-one degree. -/
theorem omegaOne_root_pow : tameUniformizerRoot v ^ (p ^ 1 - 1) =
    algebraMap Kv (AlgebraicClosure Kv) (tameUniformizer v).1 := by
  simpa only [pow_one, LocalCyclotomic.residue_natCard] using tameUniformizerRoot_spec v

/-- The niveau-one root character in the algebraic closure of Fp. -/
noncomputable def omegaOne : localInertiaGroup v →* (AlgebraicClosure (ZMod p))ˣ :=
  fundamentalCharacter v p 1 (by omega) (tameUniformizer_spec v) (omegaOne_root_pow p)
    (levelEmbedding k p 1 (by omega))

/-- The mod-p cyclotomic character, defined from the actual action on roots of unity. -/
noncomputable def modCyclotomic : Field.absoluteGaloisGroup Kv →* (ZMod p)ˣ :=
  (modularCyclotomicCharacter (AlgebraicClosure Kv)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity _ p)).comp
    { toFun := fun σ ↦ σ.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }

/-- The first fundamental character equals the local mod-p cyclotomic character. -/
theorem fundamentalCharacter_one_eq_cyclotomic :
    omegaOne p = (Units.map (algebraMap (ZMod p)
      (AlgebraicClosure (ZMod p))).toMonoidHom).comp
      ((modCyclotomic p).comp (localInertiaGroup v).subtype) := by
  ext σ
  let a := ((LocalCyclotomic.inertiaCharacter p σ : (ZMod p)ˣ) : ZMod p).val
  have hc : (levelCharacter v p 1 (by omega) (tameUniformizer_spec v)
      (omegaOne_root_pow p) σ : levelField k p 1) = a := by
    apply Subtype.ext
    exact LocalCyclotomic.residue_kummerRatioIntegral p σ
  change levelEmbedding k p 1 (by omega)
    (levelCharacter v p 1 (by omega) (tameUniformizer_spec v) (omegaOne_root_pow p) σ) = _
  rw [hc, map_natCast]
  change (a : AlgebraicClosure (ZMod p)) =
    algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
      ((LocalCyclotomic.inertiaCharacter p σ : (ZMod p)ˣ) : ZMod p)
  rw [← ZMod.natCast_zmod_val ((LocalCyclotomic.inertiaCharacter p σ : (ZMod p)ˣ) : ZMod p),
    map_natCast]

end LocalRoot
