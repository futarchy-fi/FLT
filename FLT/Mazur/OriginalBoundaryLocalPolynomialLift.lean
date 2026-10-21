/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryAffineAssociatedLift
public import FLT.Mazur.ScalarLocalPolynomialTests

/-!
# Full original arrows from equations in source stalks

The finite differential generators and their scalar equations may vary with
each associated prime of each affine test chart. Only stalkwise equations are
required. The resulting arrows cover the entire nonreduced test and retain the
original comparison and both endpoints. Coverage remains a geometric input.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeScalarImageQuotient FlatScalarFunctionPushout
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsAffine A] [Etale p]
  [IsLocallyNoetherian B]
  (e : CategoryTheory.EquivalenceRelation p q) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local instance localPolynomialBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "s" => RingHom.kerLift (FlatScalarFunctionPushout.scalarMap f)
attribute [local irreducible] scalarMorphism

include e

/-- Local equations at every affine associated prime construct the full original arrow. -/
theorem originalBoundary_lift_of_associated_local_polynomials
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Set.range t ⊆ Set.range c)
    (hP : ∀ j, ∀ Q : PrimeSpectrum Γ(B.affineCover.X j, ⊤),
      Q.asIdeal ∈ associatedPrimes Γ(B.affineCover.X j, ⊤) Γ(B.affineCover.X j, ⊤) →
      ScalarLocalPolynomialTests.Test s
        ((B.affineCover.f j ≫ t) ≫ pullback.snd f f).appTop.hom Q) :
    ∃! d : B ⟶ pullback p J.subschemeι, d ≫ c = t := by
  apply originalBoundary_unique_lift_of_affine_associated_differentials e J hJ t h
  intro j Q hQ
  exact ScalarLocalPolynomialTests.exists_annihilator s
    ((B.affineCover.f j ≫ t) ≫ pullback.snd f f).appTop.hom
    ⟨Q, hQ.isPrime⟩ (hP j ⟨Q, hQ.isPrime⟩ hQ)

/-- Finite differentials supply the finite tests from pointwise source-stalk equations. -/
theorem originalBoundary_lift_of_finite_differentials_local_polynomials
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Set.range t ⊆ Set.range c)
    (hfg : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      Module.Finite Γ(J.subscheme, ⊤) (KaehlerDifferential (Scalars f) Γ(J.subscheme, ⊤)))
    (hP : ∀ j, ∀ Q : PrimeSpectrum Γ(B.affineCover.X j, ⊤),
      Q.asIdeal ∈ associatedPrimes Γ(B.affineCover.X j, ⊤) Γ(B.affineCover.X j, ⊤) →
      ∀ z : Γ(J.subscheme, ⊤), ∃ P : Polynomial (Scalars f),
        ScalarLocalPolynomialTests.Equation s
          ((B.affineCover.f j ≫ t) ≫ pullback.snd f f).appTop.hom Q z P) :
    ∃! d : B ⟶ pullback p J.subschemeι, d ≫ c = t := by
  apply originalBoundary_lift_of_associated_local_polynomials e J hJ t h
  intro j Q hQ
  exact ScalarLocalPolynomialTests.test_of_finite_differentials s
    ((B.affineCover.f j ≫ t) ≫ pullback.snd f f).appTop.hom Q hfg (hP j Q hQ)

/-- Essential finite type also constructs full arrows from these local polynomial equations. -/
theorem originalBoundary_lift_of_essFiniteType_local_polynomials
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Set.range t ⊆ Set.range c)
    (hft : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      Algebra.EssFiniteType (Scalars f) Γ(J.subscheme, ⊤))
    (hP : ∀ j, ∀ Q : PrimeSpectrum Γ(B.affineCover.X j, ⊤),
      Q.asIdeal ∈ associatedPrimes Γ(B.affineCover.X j, ⊤) Γ(B.affineCover.X j, ⊤) →
      ∀ z : Γ(J.subscheme, ⊤), ∃ P : Polynomial (Scalars f),
        ScalarLocalPolynomialTests.Equation s
          ((B.affineCover.f j ≫ t) ≫ pullback.snd f f).appTop.hom Q z P) :
    ∃! d : B ⟶ pullback p J.subschemeι, d ≫ c = t := by
  let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
  let _ := hft
  exact originalBoundary_lift_of_finite_differentials_local_polynomials e J hJ t h
    inferInstance hP

end FLT.Mazur.EquivalenceRelationOrderedFrames
