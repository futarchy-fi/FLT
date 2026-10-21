/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryAffineAssociatedLift
public import FLT.Mazur.ScalarLocalJacobianAnnihilator

/-!
# Full original arrows from local coupled scalar equations

Nonsingular residue Jacobians at all affine associated primes construct the
entire original comparison arrow. Equations need hold only in source stalks,
and the chosen elements need generate only the relative differentials. Both
the generators and equations may vary with the affine chart and test prime.
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
local instance localJacobianBoundary_affine : IsAffine J.subscheme :=
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

/-- Local coupled equations at all associated primes construct the full original arrow. -/
theorem originalBoundary_lift_of_associated_local_jacobians
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Set.range t ⊆ Set.range c)
    (hP : ∀ j, ∀ Q : PrimeSpectrum Γ(B.affineCover.X j, ⊤),
      Q.asIdeal ∈ associatedPrimes Γ(B.affineCover.X j, ⊤) Γ(B.affineCover.X j, ⊤) →
      ScalarLocalJacobianTests.Test s
        ((B.affineCover.f j ≫ t) ≫ pullback.snd f f).appTop.hom Q) :
    ∃! d : B ⟶ pullback p J.subschemeι, d ≫ c = t := by
  apply originalBoundary_unique_lift_of_affine_associated_differentials e J hJ t h
  intro j Q hQ
  exact ScalarLocalJacobianTests.exists_annihilator s
    ((B.affineCover.f j ≫ t) ≫ pullback.snd f f).appTop.hom
    ⟨Q, hQ.isPrime⟩ (hP j ⟨Q, hQ.isPrime⟩ hQ)

end FLT.Mazur.EquivalenceRelationOrderedFrames
