/-
Copyright (c) 2026 Kelvin Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelvin Santos
-/
module

public import FLT.AbsoluteGaloisGroup.LocalCyclotomicInertia
public import FLT.AbsoluteGaloisGroup.Unramified

/-!
# Surjectivity of the local cyclotomic inertia character

Finite cyclotomic inertia is the full Galois group. Restriction from absolute
inertia and naturality of the modular character therefore give surjectivity.
-/

@[expose] public noncomputable section

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace LocalCyclotomic

variable (p : ℕ) [Fact p.Prime]
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (rationalPlace p)
local notation "Ω" => AlgebraicClosure Kv

set_option backward.isDefEq.respectTransparency.types false in
/-- Cyclotomic irreducibility transported to the chosen rational completion. -/
theorem completion_cyclotomic_irreducible :
    Irreducible (Polynomial.cyclotomic p Kv) := by
  let e : ℚ_[p] ≃+* Kv := (Padic.adicCompletionEquiv
    (NumberField.RingOfIntegers ℚ) ⟨p, Fact.out⟩).toAlgEquiv.toRingEquiv
  have h := (MulEquiv.irreducible_iff (f := (Polynomial.mapEquiv e).toMulEquiv)).mpr
    (cyclotomic_irreducible p)
  change Irreducible ((Polynomial.cyclotomic p ℚ_[p]).map e.toRingHom) at h
  simpa only [Polynomial.map_cyclotomic] using h

/-- The modular cyclotomic character on local absolute inertia is surjective. -/
theorem inertiaCharacter_surjective : Function.Surjective (inertiaCharacter p) := by
  intro a
  let L := completionCyclotomicField p
  let e := IsCyclotomicExtension.autEquivPow L (completion_cyclotomic_irreducible p)
  obtain ⟨τ, hτ⟩ := e.surjective a
  have hmap : (localInertiaGroup (rationalPlace p)).map (AlgEquiv.restrictNormalHom L) = ⊤ := by
    rw [map_localInertiaGroup_eq_inertia, completion_inertia_eq_top p L]
  obtain ⟨σ, hσ, hστ⟩ := (show τ ∈
    (localInertiaGroup (rationalPlace p)).map (AlgEquiv.restrictNormalHom L) by rw [hmap]; trivial)
  refine ⟨⟨σ, hσ⟩, ?_⟩
  have hnat := modularCyclotomicCharacter.naturality L.val.toRingHom
    τ.toRingEquiv σ.toRingEquiv
    (fun x ↦ by rw [← hστ]; exact AlgEquiv.restrictNormal_commutes σ L x)
    (IsCyclotomicExtension.zeta_spec p Kv L).card_rootsOfUnity
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω p)
  change modularCyclotomicCharacter Ω _ σ.toRingEquiv = a
  rw [← hnat]
  have he := (IsCyclotomicExtension.zeta_spec p Kv L).autToPow_eq_modularCyclotomicCharacter
    p Kv τ
  exact he.symm.trans hτ

end LocalCyclotomic
