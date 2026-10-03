/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.FundamentalCyclotomic
public import FLT.AbsoluteGaloisGroup.RootCharacterUniformizer

/-!
# Cyclotomic norms in the original geometric residue field

The comparison uses the actual action on roots of unity, for arbitrary
uniformizers and roots. It does not choose a cyclotomic generator first.
-/

@[expose] public noncomputable section
namespace LocalRoot
open IsLocalRing

variable (p : ℕ) [Fact p.Prime]
local notation "v" => LocalCyclotomic.rationalPlace p
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "O" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "Ω" => AlgebraicClosure Kv
local notation "k" => ResidueField (IntegralClosure O Ω)
attribute [local instance] rationalResidue_charP

/-- Embed the actual mod-p cyclotomic value in the original geometric residue. -/
def residueCyclotomic : localInertiaGroup v →* kˣ :=
  (Units.map (ZMod.castHom (dvd_refl p) k).toMonoidHom).comp
    ((modCyclotomic p).comp (localInertiaGroup v).subtype)

/-- Every niveau-one uniformizer-root character is the actual cyclotomic character. -/
theorem character_one_eq_residueCyclotomic {π : O}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : Ω} (hn : 0 < p - 1) (hα : α ^ (p - 1) = algebraMap Kv Ω π.1) :
    character v hn
      (fun h ↦ IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero
        hπ (Subtype.ext h)) hα = residueCyclotomic p := by
  have ht : tameUniformizerRoot v ^ (p - 1) =
      algebraMap Kv Ω (tameUniformizer v).1 := by
    simpa only [pow_one] using omegaOne_root_pow p
  rw [character_uniformizer_independent v hn (tameUniformizer_spec v) hπ ht hα]
  ext σ
  change residue (IntegralClosure O Ω) (kummerRatioIntegral v σ) =
    (ZMod.castHom (dvd_refl p) k) ((modCyclotomic p σ.1 : (ZMod p)ˣ) : ZMod p)
  rw [LocalCyclotomic.residue_kummerRatioIntegral]
  change (((LocalCyclotomic.inertiaCharacter p σ : (ZMod p)ˣ) : ZMod p).val : k) =
    (ZMod.castHom (dvd_refl p) k)
      ((LocalCyclotomic.inertiaCharacter p σ : (ZMod p)ˣ) : ZMod p)
  conv_rhs =>
    rw [← ZMod.natCast_zmod_val ((LocalCyclotomic.inertiaCharacter p σ : (ZMod p)ˣ) : ZMod p)]
  rw [map_natCast]

/-- The norm of any niveau-two root character is the actual cyclotomic character. -/
theorem character_two_norm_eq_residueCyclotomic {π : O}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : Ω} (hn : 0 < p * p - 1)
    (hα : α ^ (p * p - 1) = algebraMap Kv Ω π.1) (σ : localInertiaGroup v) :
    character v hn
      (fun h ↦ IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero
        hπ (Subtype.ext h)) hα σ ^ (p + 1) = residueCyclotomic p σ := by
  have hp := (Fact.out : p.Prime).one_lt
  have h1 : 0 < p - 1 := by omega
  have hd : (p - 1) * (p + 1) = p * p - 1 := by
    have := Nat.sub_add_cancel (by omega : 1 ≤ p)
    have := Nat.sub_add_cancel (by nlinarith : 1 ≤ p * p)
    nlinarith
  have hα' : α ^ ((p - 1) * (p + 1)) = algebraMap Kv Ω π.1 := by rwa [hd]
  have h := character_degree_mul v h1
    (fun h ↦ IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero
      hπ (Subtype.ext h)) (p + 1) (by omega) hα' σ
  rw [character_one_eq_residueCyclotomic p hπ h1] at h
  simpa only [hd] using h

end LocalRoot
