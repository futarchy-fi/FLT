/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.CyclotomicInertiaDetection
public import FLT.Deformations.RepresentationTheory.SelfTwistTrace
public import FLT.AbsoluteGaloisGroup.FundamentalCyclotomic

/-!
# Cyclotomic restriction detected at the same nonzero-trace generator

Use the full cyclotomic order of the spectrum's inertia element. No second
inertia detector is selected. Characteristic two is excluded explicitly.
-/

@[expose] public noncomputable section
namespace CyclotomicQuadratic

variable (p : ℕ) [Fact p.Prime] {k : Type*} [Field k]
local notation "v" => LocalCyclotomic.rationalPlace p
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "j" => Field.absoluteGaloisGroup.map (algebraMap ℚ Kv)

/-- A supplied local cyclotomic generator detects every nontrivial quadratic quotient character. -/
theorem eq_neg_one_of_inertia_order
    (σ : localInertiaGroup v) (hσ : orderOf (LocalRoot.modCyclotomic p σ.1) = p - 1)
    (χ : Field.absoluteGaloisGroup ℚ →* kˣ) (hχ : χ ≠ 1)
    (hker : ∀ g : (character p).ker, χ g = 1) (hsq : ∀ g, χ g ^ 2 = 1) :
    χ (j σ.1) = -1 := by
  have ht : Subgroup.zpowers (LocalRoot.modCyclotomic p σ.1) = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top _).mp
    rw [Nat.card_zpowers, hσ, Nat.card_eq_fintype_card, ZMod.card_units]
  apply eq_neg_one_of_generator p χ hχ hker hsq (j σ.1)
  intro b
  have hb : b.1 ∈ Subgroup.zpowers (LocalRoot.modCyclotomic p σ.1) := by rw [ht]; trivial
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨n, Subtype.ext ?_⟩
  change character p (j σ.1) ^ n = b.1
  rw [character_map_local]
  exact hn

variable {V : Type*} [IsAlgClosed k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- Nonzero trace at the supplied cyclotomic generator excludes reducible restriction. -/
theorem irreducible_restriction_of_inertia_trace
    (ρ : Representation k (Field.absoluteGaloisGroup ℚ) V)
    (hV : Module.finrank k V = 2) (hchar : (2 : k) ≠ 0) (hirr : ρ.IsIrreducible)
    (σ : localInertiaGroup v) (hσ : orderOf (LocalRoot.modCyclotomic p σ.1) = p - 1)
    (ht : LinearMap.trace k V (ρ (j σ.1)) ≠ 0) :
    Representation.IsIrreducible (ρ.comp (character p).ker.subtype) := by
  by_contra hres
  obtain ⟨χ, hχ, hker, hsq, e, he⟩ :=
    ρ.exists_quadratic_selfTwist (character p).ker hV hchar hirr hres
  have hneg := eq_neg_one_of_inertia_order p σ hσ χ hχ hker hsq
  have hone := ρ.selfTwist_eq_one_of_trace_ne_zero χ e he (j σ.1) ht
  have hbad : (-1 : k) = 1 := congrArg Units.val (hneg.symm.trans hone)
  exact hchar (by linear_combination -hbad)

end CyclotomicQuadratic
