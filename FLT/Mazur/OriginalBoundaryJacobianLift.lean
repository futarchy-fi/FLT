/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryGlobalDifferentialLift
public import FLT.Mazur.OriginalBoundaryAffineAssociatedLift
public import FLT.Mazur.ScalarDifferentialJacobianAnnihilator

/-!
# Full original boundary arrows from coupled Jacobian equations

Square systems of scalar equations for algebra generators produce principal
arrow neighborhoods. Nonsingular residue Jacobians at every associated affine
prime construct the full arrow on the entire nonreduced test. The equations
may vary with the prime, with no complete-intersection or finite-presentation
hypothesis. Actual comparison coverage is still required.
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
local instance jacobianLiftBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "s" => RingHom.kerLift (FlatScalarFunctionPushout.scalarMap f)
attribute [local irreducible] scalarMorphism
variable {ι : Type} (z : ι → Γ(J.subscheme, ⊤))

include e

/-- Coupled generator equations construct full arrows on their Jacobian determinant open. -/
theorem originalBoundary_jacobian_principal_lift [Fintype ι] [DecidableEq ι]
    (hz : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      Algebra.adjoin (Scalars f) (Set.range z) = ⊤)
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Set.range t ⊆ Set.range c) (P : ι → MvPolynomial ι (Scalars f))
    (hP : ∀ i, MvPolynomial.eval₂ s z (P i) = 0) :
    ∃ d : (B.basicOpen ((t ≫ pullback.snd f f).appTop
      (Matrix.det (fun i j ↦ MvPolynomial.eval₂ s z (MvPolynomial.pderiv j (P i)))))).toScheme ⟶
        pullback p J.subschemeι,
      d ≫ c = (B.basicOpen ((t ≫ pullback.snd f f).appTop
        (Matrix.det (fun i j ↦ MvPolynomial.eval₂ s z (MvPolynomial.pderiv j (P i)))))).ι ≫ t := by
  let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
  apply (originalBoundary_localNoetherian_differential_principal_lift e J hJ t h _ ?_).exists
  exact ScalarDifferentialJacobianAnnihilator.jacobian_mem_annihilator z P hz hP

/-- Nonsingular residue Jacobians include embedded primes and construct the entire full arrow. -/
theorem originalBoundary_lift_of_associated_jacobians [Fintype ι] [DecidableEq ι]
    (hz : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      Algebra.adjoin (Scalars f) (Set.range z) = ⊤)
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Set.range t ⊆ Set.range c)
    (hP : ∀ j, ∀ Q : PrimeSpectrum Γ(B.affineCover.X j, ⊤),
      Q.asIdeal ∈ associatedPrimes Γ(B.affineCover.X j, ⊤) Γ(B.affineCover.X j, ⊤) →
      ∃ P : ι → MvPolynomial ι (Scalars f),
        (∀ i, MvPolynomial.eval₂ s z (P i) = 0) ∧
        Matrix.det (Matrix.map (fun i k ↦ MvPolynomial.eval₂ s z (MvPolynomial.pderiv k (P i)))
          ((algebraMap Γ(B.affineCover.X j, ⊤) Q.asIdeal.ResidueField).comp
            ((B.affineCover.f j ≫ t) ≫ pullback.snd f f).appTop.hom)) ≠ 0) :
    ∃! d : B ⟶ pullback p J.subschemeι, d ≫ c = t := by
  let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
  apply originalBoundary_unique_lift_of_affine_associated_differentials e J hJ t h
  intro j Q hQ
  obtain ⟨P, hp, hs⟩ := hP j ⟨Q, hQ.isPrime⟩ hQ
  refine ⟨_, ScalarDifferentialJacobianAnnihilator.jacobian_mem_annihilator z P hz hp, ?_⟩
  exact ScalarDifferentialJacobianAnnihilator.determinant_not_mem
    ((B.affineCover.f j ≫ t) ≫ pullback.snd f f).appTop.hom ⟨Q, hQ.isPrime⟩ _ hs

end FLT.Mazur.EquivalenceRelationOrderedFrames
