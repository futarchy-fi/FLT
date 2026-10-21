/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryGlobalDifferentialLift
public import FLT.Mazur.OriginalBoundaryAffineAssociatedLift
public import FLT.Mazur.ScalarPolynomialResidueRigidity

/-!
# Full original arrows from explicit scalar polynomial equations

Generator equations over the exact scalar-image algebra construct principal
arrow neighborhoods. Residue-separable equations at all associated affine
primes construct an arrow on the whole test. Polynomials may vary with the
prime, and embedded primes are included. Comparison coverage remains a
separate geometric input; equality of endpoint ranks does not replace it.
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
local instance polynomialLiftBoundary_affine : IsAffine J.subscheme :=
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

/-- Explicit generator equations construct full arrows on their derivative-product opens. -/
theorem originalBoundary_polynomial_principal_lift [Fintype ι]
    (hz : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      Algebra.adjoin (Scalars f) (Set.range z) = ⊤)
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Set.range t ⊆ Set.range c) (P : ι → Polynomial (Scalars f))
    (hP : ∀ i, (P i).eval₂ s (z i) = 0) :
    ∃ d : (B.basicOpen ((t ≫ pullback.snd f f).appTop
      (∏ i, (P i).derivative.eval₂ s (z i)))).toScheme ⟶ pullback p J.subschemeι,
      d ≫ c = (B.basicOpen ((t ≫ pullback.snd f f).appTop
        (∏ i, (P i).derivative.eval₂ s (z i)))).ι ≫ t := by
  let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
  apply (originalBoundary_localNoetherian_differential_principal_lift e J hJ t h _ ?_).exists
  exact ScalarDifferentialPolynomialAnnihilator.product_mem_annihilator z P hz hP

/-- Associated residue-separable equations construct the whole original arrow on a full test. -/
theorem originalBoundary_lift_of_associated_polynomials [Finite ι]
    (hz : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      Algebra.adjoin (Scalars f) (Set.range z) = ⊤)
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Set.range t ⊆ Set.range c)
    (hP : ∀ j, ∀ Q : PrimeSpectrum Γ(B.affineCover.X j, ⊤),
      Q.asIdeal ∈ associatedPrimes Γ(B.affineCover.X j, ⊤) Γ(B.affineCover.X j, ⊤) →
      ∃ P : ι → Polynomial (Scalars f),
        (∀ i, (P i).eval₂ s (z i) = 0) ∧
        ∀ i, ((P i).map (((algebraMap Γ(B.affineCover.X j, ⊤)
          Q.asIdeal.ResidueField).comp
          ((B.affineCover.f j ≫ t) ≫ pullback.snd f f).appTop.hom).comp s)).Separable) :
    ∃! d : B ⟶ pullback p J.subschemeι, d ≫ c = t := by
  let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
  apply originalBoundary_unique_lift_of_affine_associated_differentials e J hJ t h
  intro j Q hQ
  obtain ⟨P, hp, hs⟩ := hP j ⟨Q, hQ.isPrime⟩ hQ
  exact ScalarPolynomialResidueRigidity.exists_annihilator
    ((B.affineCover.f j ≫ t) ≫ pullback.snd f f).appTop.hom ⟨Q, hQ.isPrime⟩
    z P hz hp hs

end FLT.Mazur.EquivalenceRelationOrderedFrames
