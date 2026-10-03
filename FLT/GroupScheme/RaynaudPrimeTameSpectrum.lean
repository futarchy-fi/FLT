/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudRationalCharpoly
public import FLT.AbsoluteGaloisGroup.NiveauTwoInertiaGenerator
public import FLT.Deformations.RepresentationTheory.MappedTameSpectrum

/-!
# The original prime-field rank-two finite-flat tame spectrum

The original flat model constructs the tower and binary factor charpolys.
Choose a niveau-two inertia generator first; its actual cyclotomic norm and
the original determinant select the spectrum. The small primes are excluded.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ThreeAdicPlan
open NumberField IsLocalRing Polynomial

variable (p : ℕ) [Fact p.Prime]
local notation "v" => LocalCyclotomic.rationalPlace p
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "O" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "Ω" => AlgebraicClosure Kv
local notation "k" => ResidueField (IntegralClosure O Ω)
attribute [local instance] LocalRoot.rationalResidue_charP

set_option maxHeartbeats 1600000 in
-- Assemble the two actual factor cases and the original cyclotomic determinant.
/-- Flatness and the actual cyclotomic determinant give the prime-field tame spectrum. -/
theorem prime_flat_tame_spectrum (hp : 3 < p)
    (M : FF O Kv) [Module (ZMod p) M.Points]
    (ρ : Representation (ZMod p) (localInertiaGroup v) M.Points)
    (hρ : ρ.IsDiscreteContinuous) (hact : ∀ σ w, ρ σ w = σ • w)
    (hdim : Module.finrank (ZMod p) M.Points = 2)
    (hdet : ∀ σ : localInertiaGroup v,
      (ρ σ).det = ((LocalRoot.modCyclotomic p σ.1 : (ZMod p)ˣ) : ZMod p)) :
    ∃ σ : localInertiaGroup v,
      orderOf (LocalRoot.modCyclotomic p σ.1) = p - 1 ∧
      ∃ a b : kˣ,
        (ρ σ).charpoly.map (ZMod.castHom (dvd_refl p) k) =
          (X - C (a : k)) * (X - C (b : k)) ∧
        (orderOf (a / b) = p - 1 ∨ orderOf (a / b) = p + 1) ∧
        LinearMap.trace (ZMod p) M.Points (ρ σ) ≠ 0 := by
  have hπ : Valued.v ((p : O) : Kv) = Multiplicative.ofAdd (-1 : ℤ) :=
    LocalCyclotomic.rationalPrime_valuation p
  have hn : 0 < p - 1 := by omega
  have hn2 : 0 < p * p - 1 := Nat.sub_pos_of_lt (by nlinarith)
  have hp0 : (p : Kv) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap Kv Ω (p : Kv)) hn
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap Kv Ω (p : Kv)) hn2
  obtain ⟨σ, hz, hnorm, hcyc, hratio⟩ :=
    LocalRoot.exists_niveauTwo_inertia_generator p hπ hn2 hβ
  let z := LocalRoot.character v hn2 hp0 hβ σ
  let c := LocalRoot.residueCyclotomic p σ
  have hz' : orderOf z = p * p - 1 := hz
  have hc : orderOf c = p - 1 := (LocalRoot.residueCyclotomic_order p σ).trans hcyc
  have hn' : z ^ (p + 1) = c := hnorm
  let f := ZMod.castHom (dvd_refl p) k
  have hd : f (ρ σ).det = (c : k) := congrArg f (hdet σ)
  have h1 : LocalRoot.character v hn hp0 hα σ = c :=
    congrArg (fun χ : localInertiaGroup v →* kˣ ↦ χ σ)
      (LocalRoot.character_one_eq_residueCyclotomic p hπ hn hα)
  refine ⟨σ, hcyc, ?_⟩
  rcases rational_rank_two_charpoly p M ρ hρ hact hdim hn hn2 hp0 hα hβ with
    ⟨a, b, ha, hb, hf⟩ | ⟨a, b, ha, hb, hf⟩
  · have hf' := hf σ
    rw [h1] at hf'
    have hs := Representation.ordinary_map_charpoly_of_digits (ρ σ) f hdim hp hc ha hb hd hf'
    refine ⟨1, c, hs, Or.inl ?_, ?_⟩
    · simpa only [one_div, orderOf_inv] using hc
    · intro ht
      have htr := ((ρ σ).trace_det_of_map_charpoly_factors f hdim 1 (c : k) hs).1
      rw [ht, map_zero] at htr
      exact Representation.ordinary_sum_ne_zero hp hc htr.symm
  · have hd' : f (ρ σ).det = ((z ^ (p + 1) : kˣ) : k) := by rw [hn']; exact hd
    have hs := Representation.niveau_two_map_charpoly_of_digits (ρ σ) f hdim hp hz'
      ha hb hd' (hf σ)
    refine ⟨z, z ^ p, hs, Or.inr hratio, ?_⟩
    intro ht
    have htr := ((ρ σ).trace_det_of_map_charpoly_factors f hdim _ _ hs).1
    rw [ht, map_zero] at htr
    exact Representation.niveau_two_sum_ne_zero (by omega : 1 < p) hz' htr.symm

end ThreeAdicPlan
