/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.EllipticCurve.Torsion
public import FLT.GaloisRepresentation.Automorphic
public import FLT.GaloisRepresentation.HardlyRamified.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Unramified.Locus

/-!
# The Moret--Bailly potential-modularity interface

This file records the application-shaped Moret--Bailly statement used in the potential
modularity argument. The formulation follows Snowden's seminar notes, Lecture 26,
Theorem 9 and Propositions 10 and 13, and the approximation theorem of Moret-Bailly,
*Groupes de Picard et problèmes de Skolem II* (1989).
-/

@[expose] public section

open IsDedekindDomain NumberField
open scoped TensorProduct

universe u

/-- The canonical reduction map from the `p`-adic integers to the prime field. -/
noncomputable local instance moretBaillyAlgebra (p : ℕ) [Fact p.Prime] :
    Algebra ℤ_[p] (ZMod p) :=
  RingHom.toAlgebra PadicInt.toZMod

/-- Classical decidable equality used to construct elliptic-curve torsion representations. -/
noncomputable local instance moretBaillyDecidableEq (K : Type*) : DecidableEq K :=
  Classical.typeDecidableEq K

namespace GaloisRep

/-- A representation is induced from an imaginary-quadratic character if there exist a
quadratic, totally complex extension `K/F` and a one-dimensional representation of
`Gal(K̅/K)` inducing it. The extension is intentionally existential, as in Snowden,
Lecture 26, Proposition 13. -/
@[nolint unusedArguments]
def IsInducedFromImaginaryQuadraticCharacter
    {F : Type u} [Field F] [NumberField F] [IsTotallyReal F]
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {V : Type*} [AddCommGroup V] [Module A V]
    (ρ : GaloisRep F A V) : Prop :=
  ∃ (K : Type u) (_ : Field K) (_ : NumberField K)
    (_ : Algebra F K) (_ : Algebra.IsQuadraticExtension F K)
    (_ : IsTotallyComplex K) (χ : GaloisRep K A A),
    ρ.IsInducedFromCharacter χ

end GaloisRep

namespace WeierstrassCurve

/-- `E` has good ordinary reduction above `p` if it has good reduction at every place
above `p` and `p` does not divide the local Frobenius trace there. Since coefficient one
of `localPolynomial` is the negative trace, this is the usual ordinary criterion. The
universal quantifier records the "all places" condition in Snowden, Lecture 26,
Proposition 10. -/
noncomputable def HasGoodOrdinaryReductionAbove
    {F : Type u} [Field F] [NumberField F]
    (E : WeierstrassCurve F) (p : ℕ) : Prop :=
  ∀ v : HeightOneSpectrum (RingOfIntegers F),
    (p : RingOfIntegers F) ∈ v.asIdeal →
    let E_v := E.baseChange (v.adicCompletion F)
    E_v.HasGoodReduction (v.adicCompletionIntegers F) ∧
      ¬ (p : ℤ) ∣ (E_v.localPolynomial (v.adicCompletionIntegers F)).coeff 1

end WeierstrassCurve

namespace MoretBailly

/-- The application-shaped Moret--Bailly statement used for potential modularity.

The coefficient field is exactly the prime field `ZMod ℓ`; this is the hypothesis
required by Snowden, Lecture 26, Remark 11 for the elliptic-curve formulation. The
conclusion packages the disjointness and ramification control of Theorem 9, the
elliptic-curve realization and good ordinary reduction of Proposition 10, and the
auxiliary induced representation of Proposition 13. Its geometric existence proof is
the deferred Moret-Bailly 1989 input. -/
theorem statement
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓOdd : Odd ℓ)
    (ρ : GaloisRep ℚ (ZMod ℓ) (Fin 2 → ZMod ℓ))
    (hdim : Module.rank (ZMod ℓ) (Fin 2 → ZMod ℓ) = 2)
    (_hρ : GaloisRepresentation.IsHardlyRamified hℓOdd hdim ρ)
    (Kavoid : Type u) [Field Kavoid] [NumberField Kavoid] :
    ∃ (F : Type u) (_ : Field F) (_ : NumberField F) (_ : Algebra ℚ F)
      (_ : IsGalois ℚ F) (_ : IsTotallyReal F),
      Even (Module.finrank ℚ F) ∧
      IsDomain (F ⊗[ℚ] Kavoid) ∧
      Algebra.IsUnramifiedIn (RingOfIntegers F) (Ideal.span {(ℓ : ℤ)} : Ideal ℤ) ∧
      ∃ (p : ℕ) (_ : Fact p.Prime) (E : WeierstrassCurve F) (_ : E.IsElliptic),
        p ≠ ℓ ∧
        (∃ e : ((E.map (algebraMap F (AlgebraicClosure F))).nTorsion ℓ) ≃ₗ[ZMod ℓ]
            (Fin 2 → ZMod ℓ),
          (E.galoisRep ℓ (Fact.out : ℓ.Prime).pos).conj e = ρ.map (algebraMap ℚ F)) ∧
        GaloisRep.IsInducedFromImaginaryQuadraticCharacter
          (E.galoisRep p (Fact.out : p.Prime).pos) ∧
        E.HasGoodOrdinaryReductionAbove ℓ ∧
        E.HasGoodOrdinaryReductionAbove p := by
  sorry

end MoretBailly
