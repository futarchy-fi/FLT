/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryLocalPolynomialLift
public import FLT.Mazur.OriginalBoundaryLocalJacobianLift
public import FLT.Mazur.OriginalBoundaryRankAssociatedLift

/-!
# Whole original rank-stage arrows from source-stalk equations

The original rank construction supplies endpoint finiteness. Generic comparison
coverage together with finite local polynomial or Jacobian tests at all affine
associated primes then gives the unique arrow on the full nonreduced rank stage.
Global algebra generators and globally vanishing equations are unnecessary.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeScalarImageQuotient FlatScalarFunctionPushout
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsAffine A]
  [Etale p] [IsSeparated p] [QuasiCompact p] [LocallyQuasiFinite p]
  [IsLocallyNoetherian A] [IsLocallyNoetherian B]
  (e : CategoryTheory.EquivalenceRelation p q) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local instance rankLocalOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance rankLocalOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance rankLocalOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local instance rankLocalBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "s" => RingHom.kerLift (FlatScalarFunctionPushout.scalarMap f)
attribute [local irreducible] scalarMorphism rankPullbackThickening rankPullbackMap
  rankThickening rankThickeningMap
variable (t : B ⟶ pullback
  (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))
  (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤))))
  (n k : ℕ)
local notation "S" => rankPullbackThickening (Over.mk p) (t ≫ x) n k
local notation "v" => rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t

include e

/-- Local separable equations and generic coverage construct the whole original rank arrow. -/
theorem originalBoundary_rankStage_lift_of_generic_local_polynomials
    (h : genericPoints S ⊆ v ⁻¹' Set.range c)
    (hP : ∀ j, ∀ Q : PrimeSpectrum Γ((S).affineCover.X j, ⊤),
      Q.asIdeal ∈ associatedPrimes Γ((S).affineCover.X j, ⊤) Γ((S).affineCover.X j, ⊤) →
      ScalarLocalPolynomialTests.Test s
        (((S).affineCover.f j ≫ v) ≫ pullback.snd f f).appTop.hom Q) :
    ∃! d : S ⟶ pullback p J.subschemeι, d ≫ c = v := by
  let _ : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian
    (rankPullbackMap (Over.mk p) (t ≫ x) n k)
  let _ := originalBoundary_rankStage_endpoint_finite J t n k
  exact originalBoundary_lift_of_associated_local_polynomials e J hJ v
    (originalBoundary_rankStage_coverage_of_generic J hJ t n k h) hP

/-- Coupled equations need only hold in the source stalks to construct the full stage arrow. -/
theorem originalBoundary_rankStage_lift_of_generic_local_jacobians
    (h : genericPoints S ⊆ v ⁻¹' Set.range c)
    (hP : ∀ j, ∀ Q : PrimeSpectrum Γ((S).affineCover.X j, ⊤),
      Q.asIdeal ∈ associatedPrimes Γ((S).affineCover.X j, ⊤) Γ((S).affineCover.X j, ⊤) →
      ScalarLocalJacobianTests.Test s
        (((S).affineCover.f j ≫ v) ≫ pullback.snd f f).appTop.hom Q) :
    ∃! d : S ⟶ pullback p J.subschemeι, d ≫ c = v := by
  let _ : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian
    (rankPullbackMap (Over.mk p) (t ≫ x) n k)
  let _ := originalBoundary_rankStage_endpoint_finite J t n k
  exact originalBoundary_lift_of_associated_local_jacobians e J hJ v
    (originalBoundary_rankStage_coverage_of_generic J hJ t n k h) hP

/-- Essential finite type constructs finite tests from equations for individual source elements. -/
theorem originalBoundary_rankStage_lift_of_essFiniteType_local_polynomials
    (h : genericPoints S ⊆ v ⁻¹' Set.range c)
    (hft : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      Algebra.EssFiniteType (Scalars f) Γ(J.subscheme, ⊤))
    (hP : ∀ j, ∀ Q : PrimeSpectrum Γ((S).affineCover.X j, ⊤),
      Q.asIdeal ∈ associatedPrimes Γ((S).affineCover.X j, ⊤) Γ((S).affineCover.X j, ⊤) →
      ∀ z : Γ(J.subscheme, ⊤), ∃ P : Polynomial (Scalars f),
        ScalarLocalPolynomialTests.Equation s
          (((S).affineCover.f j ≫ v) ≫ pullback.snd f f).appTop.hom Q z P) :
    ∃! d : S ⟶ pullback p J.subschemeι, d ≫ c = v := by
  apply originalBoundary_rankStage_lift_of_generic_local_polynomials e J hJ t n k h
  intro j Q hQ
  exact ScalarLocalPolynomialTests.test_of_essFiniteType s
    (((S).affineCover.f j ≫ v) ≫ pullback.snd f f).appTop.hom Q hft (hP j Q hQ)

end FLT.Mazur.EquivalenceRelationOrderedFrames
