/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Assembly.Inputs
public import FLT.GaloisRepresentation.HardlyRamified.B5Inputs
public import Mathlib.Topology.Instances.ZMod

/-!
# Prime-field reducibility from the characteristic-zero inputs

This conditional B5 theorem assembles the proved coefficient and Frobenius
transport lemmas while retaining lifting, compatible families, and the
three-adic trace calculation as explicit propositions.
-/

@[expose] public section

open scoped TensorProduct NumberField

namespace GaloisRepresentation

open B5Inputs FLT.Assembly

/-- The natural p-adic algebra structure on the prime field. -/
noncomputable local instance primeFieldPadicAlgebra (p : ℕ) [Fact p.Prime] :
    Algebra ℤ_[p] (ZMod p) :=
  RingHom.toAlgebra PadicInt.toZMod

set_option backward.isDefEq.respectTransparency false in
/-- The three characteristic-zero inputs imply prime-field reducibility. -/
theorem IsHardlyRamified.not_isIrreducible_of_inputs
    (hlift : HardlyRamifiedLifting) (hfamily : HardlyRamifiedCompatibleFamilies)
    (hthree : ThreeAdicFrobeniusTrace)
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hpodd : Odd p)
    (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] [Module.Free (ZMod p) V]
    (hV : Module.rank (ZMod p) V = 2) (ρ : GaloisRep ℚ (ZMod p) V)
    (hρ : IsHardlyRamified hpodd hV ρ) : ¬ ρ.IsIrreducible := by
  classical
  intro hirr
  let instLocalHom : IsLocalHom (algebraMap ℤ_[p] (ZMod p)) :=
    IsLocalHom.of_surjective _ (ZMod.ringHom_surjective _)
  obtain ⟨R, _, _, _, _, _, _, _, _, _, _, _, _, W, _, _, _, _, hW, σ, e, hσ, he⟩ :=
    hlift hpodd V hV ρ hirr hρ
  obtain ⟨A, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsurj⟩ :=
    exists_domain_quotient (p := p) R (ZMod p)
  have hWA : Module.rank A (A ⊗[R] W) = 2 := by
    rw [Module.rank_baseChange, hW]
    simp
  have hσA := hardlyRamified_quotient hpodd hsurj hW hWA hσ
  obtain ⟨E, _, _, τ, hcompatible, hhardly, hinfamily⟩ :=
    hfamily hpodd hWA hσA
  let h3 : Fact (Nat.Prime 3) := ⟨by decide⟩
  let φ : E →+* AlgebraicClosure ℚ_[3] :=
    (IsAlgClosed.lift (R := ℚ) (S := E) (M := AlgebraicClosure ℚ_[3])).toRingHom
  obtain ⟨B, _, _, _, _, _, _, _, _, _, _, _, _, U, _, _, _, _, hU, η, e3, hη, he3⟩ :=
    hhardly h3 (by decide) φ
  have htrace3 : ∀ (q : ℕ) (hq : q.Prime), 5 ≤ q → q ≠ 3 →
      (τ h3 φ |>.toLocal hq.toHeightOneSpectrumRingOfIntegersRat
        (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)).trace
          _ _ = 1 + q := by
    intro q hq hq5 _
    rw [← he3, trace_toLocal_baseChange_conj, hthree U hU hη q hq hq5]
    simp
  obtain ⟨S, hS⟩ := compatible_trace τ hcompatible h3 φ htrace3
  obtain ⟨_, _, ψ, ep, hep⟩ := hinfamily
  apply not_isIrreducible_of_frobenius_traces p hp hV ρ hρ.det S ?_ hirr
  intro q hq hq5 hqp hqS
  have ht := hS (Fact.mk (Fact.out : p.Prime)) ψ q hq hq5 (by omega) hqp hqS
  rw [← hep, trace_toLocal_baseChange_conj] at ht
  have htA : ((σ.baseChange A).toLocal hq.toHeightOneSpectrumRingOfIntegersRat
      (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)).trace A _
        = 1 + q := by
    apply padic_domain_map_injective (p := p) (algebraMap A (AlgebraicClosure ℚ_[p]))
    simpa using ht
  rw [trace_toLocal_baseChange] at htA
  have htk := congrArg (algebraMap A (ZMod p)) htA
  rw [← IsScalarTower.algebraMap_apply R A (ZMod p)] at htk
  rw [← he, trace_toLocal_baseChange_conj]
  simpa using htk

end GaloisRepresentation
