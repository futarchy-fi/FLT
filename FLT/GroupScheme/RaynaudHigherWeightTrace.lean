/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudRationalHigherWeight
public import FLT.AbsoluteGaloisGroup.HigherNiveauCyclotomicNorm
public import FLT.Deformations.RepresentationTheory.HigherBinaryBounds
public import FLT.Deformations.RepresentationTheory.RankTwoScalarQuotient

/-!
# Higher weights obstruct vanishing of the original coefficient-field trace

Construct the scalar weights of an actual simple quotient of arbitrary
prime-field dimension. Cayley–Hamilton retains the original rank-two field.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ThreeAdicPlan
open NumberField IsLocalRing

variable (p : ℕ) [Fact p.Prime]
local notation "v" => LocalCyclotomic.rationalPlace p
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "O" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "Ω" => AlgebraicClosure Kv
local notation "I" => localInertiaGroup v
local notation "κ" => ResidueField (IntegralClosure O Ω)
attribute [local instance] LocalRoot.rationalResidue_charP

variable {k : Type} [Field k] [CharP k p]
  (M : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)) [Module k M.Points]
  (ρ : Representation k (localInertiaGroup (LocalCyclotomic.rationalPlace p)) M.Points)
  {W : Type} [AddCommGroup W]
  [Module (ZMod p) W]
  [DistribMulAction (localInertiaGroup (LocalCyclotomic.rationalPlace p)) W]
  (ρW : Representation (ZMod p) (localInertiaGroup (LocalCyclotomic.rationalPlace p)) W)
  [ρW.IsIrreducible]
  [TopologicalSpace (Module.End (ZMod p) W)ˣ] [DiscreteTopology (Module.End (ZMod p) W)ˣ]

set_option maxHeartbeats 1800000 in
-- Assemble the original higher model, generator, and quadratic operator equation.
/-- An actual simple quotient forces nonzero original k-linear trace at a cyclotomic generator. -/
theorem higher_quotient_trace_ne_zero (hp : 3 < p)
    (hact : ∀ σ x, ρ σ x = σ • x)
    (hρW : Continuous ρW.toHomUnits) (hactW : ∀ σ w, ρW σ w = σ • w)
    (q : M.Points →+[I] W) (hq : Function.Surjective q)
    (hdim : Module.finrank k M.Points = 2)
    (hdet : ∀ σ : I, (ρ σ).det = ZMod.castHom (dvd_refl p) k
      ((LocalRoot.modCyclotomic p σ.1 : (ZMod p)ˣ) : ZMod p)) :
    ∃ σ : I, orderOf (LocalRoot.modCyclotomic p σ.1) = p - 1 ∧
      LinearMap.trace k M.Points (ρ σ) ≠ 0 := by
  let : Finite W := Finite.of_surjective q hq
  let : Nontrivial W := IsSimpleModule.nontrivial (MonoidAlgebra (ZMod p) I) ρW.asModule
  let r : ℕ+ := ⟨Module.finrank (ZMod p) W, Module.finrank_pos⟩
  have hn : 0 < p ^ (r : ℕ) - 1 := Nat.sub_pos_of_lt
    (one_lt_pow₀ (by omega : 1 < p) r.pos.ne')
  have hp0 : (p : Kv) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap Kv Ω (p : Kv)) hn
  let idM : M.Points →+[I] M.Points :=
    { toAddMonoidHom := AddMonoidHom.id _
      map_smul' := fun _ _ ↦ rfl }
  obtain ⟨F, hF, hfin, hchar, hmod, χ, ε, d, _, hd, hχ, hw⟩ :=
    rational_original_higher_weight p M ρW hρW hactW idM q
      Function.injective_id hq r rfl hn hp0 hα
  obtain ⟨σ, hz, hnorm, hcyc⟩ := LocalRoot.exists_niveau_inertia_generator p (r := (r : ℕ))
    (π := (p : O)) (α := α) r.pos
    (LocalCyclotomic.rationalPrime_valuation p) hn hα
  refine ⟨σ, hcyc, fun ht ↦ ?_⟩
  have hs := (ρ σ).scalar_quotient_square_of_trace_eq_zero hdim ht
    (LocalRoot.modCyclotomic p σ.1 : ZMod p) (hdet σ) q.toAddMonoidHom hq (χ σ : F)
    (fun x ↦ (congrArg q (hact σ x)).trans ((q.map_smul σ x).trans (hχ σ (q x))))
  have hε : ε.comp (ZMod.castHom (dvd_refl p) F) =
      ZMod.castHom (dvd_refl p) κ := Subsingleton.elim _ _
  have hs' := congrArg ε hs
  rw [map_pow, map_neg, hw σ] at hs'
  have hc : ε (ZMod.castHom (dvd_refl p) F (LocalRoot.modCyclotomic p σ.1 : ZMod p)) =
      (LocalRoot.residueCyclotomic p σ : κ) :=
    congrArg (fun f : ZMod p →+* κ ↦ f (LocalRoot.modCyclotomic p σ.1 : ZMod p)) hε
  rw [hc, ← hnorm] at hs'
  have htwo : (2 : κ) ≠ 0 := fun h ↦
    Nat.not_dvd_of_pos_of_lt (by omega) (by omega) ((CharP.cast_eq_zero_iff κ p 2).mp h)
  apply Representation.higher_binary_square_ne_neg_norm hp r d hd htwo hz
  simpa only [← pow_mul, Nat.mul_comm _ 2, Units.val_pow_eq_pow_val] using hs'

end ThreeAdicPlan
