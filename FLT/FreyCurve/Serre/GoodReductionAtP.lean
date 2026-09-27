/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.FlatTorsion
public import FLT.FreyCurve.Serre.AtP
public import FLT.FreyCurve.Serre.LocalInertia
public import FLT.FreyCurve.Serre.StableLineQuotient

/-!
# Good reduction at the torsion prime

Good reduction and a stable line give a finite-flat character quotient of
prime torsion. `GoodReductionAtPProof` proves `GoodReductionAtPQuotient` (defined in `AtP`)
for `p ≥ 5`.
-/

@[expose] public section

open NumberField ValuativeRel

attribute [local instance] completionValuativeRel completion_isNonarchimedeanLocalField
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

/-- Classical equality for the coordinates of local geometric points. -/
noncomputable local instance goodReductionAtPDecidableEq (α : Type*) : DecidableEq α :=
  Classical.typeDecidableEq α

namespace WeierstrassCurve

/-- Over a characteristic-zero DVR, any specified stable line in the prime torsion
of an elliptic curve with good reduction has a finite-flat character quotient.
The geometric inputs are the existing torsion-cardinality and torsion-flatness
admissions. No unramifiedness of this particular quotient is asserted. -/
theorem exists_finiteFlat_character_quotient_of_goodReduction
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    (E : WeierstrassCurve K) [E.IsElliptic] [E.HasGoodReduction R]
    (p : ℕ) [Fact p.Prime]
    (i : ZMod p →ₗ[ZMod p] (E.map (algebraMap K (AlgebraicClosure K))).nTorsion p)
    (hinj : Function.Injective i)
    (hi : ∀ g, ∃ a, E.galoisRep p (Fact.out : p.Prime).pos g (i 1) = i a) :
    ∃ (χ : GaloisRep K (ZMod p) (ZMod p))
      (q : (E.map (algebraMap K (AlgebraicClosure K))).nTorsion p →ₗ[ZMod p] ZMod p),
      Function.Surjective q ∧ LinearMap.ker q = LinearMap.range i ∧
      (∀ g x, q (E.galoisRep p (Fact.out : p.Prime).pos g x) = χ g (q x)) ∧
      GaloisModule.IsFiniteFlat R K (AlgebraicClosure K) χ.Space := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨e⟩ := (E.map (algebraMap K (AlgebraicClosure K))).n_torsion_dimension
    (n := p) (by exact_mod_cast (Nat.ne_of_gt hp))
  let e' : (E.map (algebraMap K (AlgebraicClosure K))).nTorsion p ≃ₗ[ZMod p]
      ZMod p × ZMod p := { e with map_smul' := ZMod.map_smul e }
  have hdim : Module.finrank (ZMod p)
      ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion p) = 2 := by
    rw [e'.finrank_eq, Module.finrank_prod]
    simp
  obtain ⟨χ, q, hq, hker, heq⟩ :=
    (E.galoisRep p hp).exists_character_quotient_of_stableLine hdim i hinj hi
  exact ⟨χ, q, hq, hker, heq, (E.galoisRep p hp).isFiniteFlat_of_surjective χ
    (E.isFiniteFlat_torsion_of_goodReduction R K p hp) q hq heq⟩

end WeierstrassCurve
