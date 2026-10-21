/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryPolynomialLift
public import FLT.Mazur.OriginalBoundaryJacobianLift
public import FLT.Mazur.OriginalBoundaryRankAssociatedLift
public import FLT.Mazur.RelativeRankStageRecovery

/-!
# Full rank-stage arrows from concrete scalar equations

The original rank construction supplies full endpoint finiteness. Generic
comparison coverage and explicit residue polynomial or Jacobian tests then
construct unique arrows on the entire nonreduced rank stage, not only on a
chosen principal open. All such arrows respect the original order transitions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeScalarImageQuotient FlatScalarFunctionPushout
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace RankPolynomialTests
variable {R C T ι : Type} [CommRing R] [CommRing C] [CommRing T]

/-- Explicit scalar equations with separable images at every associated test prime. -/
def Separable (σ : R →+* C) (z : ι → C) (φ : C →+* T) : Prop :=
  ∀ Q : PrimeSpectrum T, Q.asIdeal ∈ associatedPrimes T T →
    ∃ P : ι → Polynomial R, (∀ i, (P i).eval₂ σ (z i) = 0) ∧
      ∀ i, ((P i).map (((algebraMap T Q.asIdeal.ResidueField).comp φ).comp σ)).Separable

/-- Coupled scalar equations with nonsingular Jacobians at every associated test prime. -/
def Jacobian [Fintype ι] [DecidableEq ι]
    (σ : R →+* C) (z : ι → C) (φ : C →+* T) : Prop :=
  ∀ Q : PrimeSpectrum T, Q.asIdeal ∈ associatedPrimes T T →
    ∃ P : ι → MvPolynomial ι R, (∀ i, MvPolynomial.eval₂ σ z (P i) = 0) ∧
      Matrix.det (Matrix.map (fun i k ↦ MvPolynomial.eval₂ σ z (MvPolynomial.pderiv k (P i)))
        ((algebraMap T Q.asIdeal.ResidueField).comp φ)) ≠ 0

end RankPolynomialTests

variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsAffine A]
  [Etale p] [IsSeparated p] [QuasiCompact p] [LocallyQuasiFinite p]
  [IsLocallyNoetherian A] [IsLocallyNoetherian B]
  (e : CategoryTheory.EquivalenceRelation p q) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local instance rankPolynomialOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance rankPolynomialOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance rankPolynomialOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local instance rankPolynomialBoundary_affine : IsAffine J.subscheme :=
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

variable {ι : Type} (z : ι → Γ(J.subscheme, ⊤))

include e

/-- Generic coverage and residue-separable equations construct the whole original rank arrow. -/
theorem originalBoundary_rankStage_lift_of_generic_polynomials [Finite ι]
    (hz : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      Algebra.adjoin (Scalars f) (Set.range z) = ⊤)
    (h : genericPoints S ⊆ v ⁻¹' Set.range c)
    (hP : ∀ j, RankPolynomialTests.Separable s z
      (((S).affineCover.f j ≫ v) ≫ pullback.snd f f).appTop.hom) :
    ∃! d : S ⟶ pullback p J.subschemeι, d ≫ c = v := by
  let _ : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian
    (rankPullbackMap (Over.mk p) (t ≫ x) n k)
  let _ := originalBoundary_rankStage_endpoint_finite J t n k
  exact originalBoundary_lift_of_associated_polynomials e J hJ z hz v
    (originalBoundary_rankStage_coverage_of_generic J hJ t n k h) hP

/-- Coupled equations and nonsingular residue Jacobians also cover the full nonreduced stage. -/
theorem originalBoundary_rankStage_lift_of_generic_jacobians [Fintype ι] [DecidableEq ι]
    (hz : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      Algebra.adjoin (Scalars f) (Set.range z) = ⊤)
    (h : genericPoints S ⊆ v ⁻¹' Set.range c)
    (hP : ∀ j, RankPolynomialTests.Jacobian s z
      (((S).affineCover.f j ≫ v) ≫ pullback.snd f f).appTop.hom) :
    ∃! d : S ⟶ pullback p J.subschemeι, d ≫ c = v := by
  let _ : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian
    (rankPullbackMap (Over.mk p) (t ≫ x) n k)
  let _ := originalBoundary_rankStage_endpoint_finite J t n k
  exact originalBoundary_lift_of_associated_jacobians e J hJ z hz v
    (originalBoundary_rankStage_coverage_of_generic J hJ t n k h) hP

omit [IsAffine A] [QuasiCompact p] [LocallyQuasiFinite p] [IsLocallyNoetherian A]
  [IsLocallyNoetherian B] in
/-- Full stage arrows, however their equations were chosen, agree along the original transitions. -/
theorem originalBoundary_fullRankStage_arrows_compatible {l : ℕ} (h : k ≤ l)
    (d : S ⟶ pullback p J.subschemeι)
    (d' : rankPullbackThickening (Over.mk p) (t ≫ x) n l ⟶ pullback p J.subschemeι)
    (hd : d ≫ c = v)
    (hd' : d' ≫ c = rankPullbackMap (Over.mk p) (t ≫ x) n l ≫ t) :
    rankStagePullbackTransition (Over.mk p) (t ≫ x) n h ≫ d' = d := by
  let _ := originalBoundaryComparison_mono e J hJ
  apply (cancel_mono c).mp
  rw [Category.assoc, hd', hd, rankStagePullbackTransition_map_assoc]

end FLT.Mazur.EquivalenceRelationOrderedFrames
