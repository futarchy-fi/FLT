/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryRankLocalEquationLift
public import FLT.Mazur.ScalarStalkJacobianTests

/-!
# Original boundary arrows from coupled source-stalk equations

Coupled equations with invertible residue Jacobians need differential generation
only in the source stalk. Finite source differentials spread these local tests.
The full test and original rank-stage arrows retain both endpoints.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeScalarImageQuotient FlatScalarFunctionPushout
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsAffine A] [Etale p]
  [IsLocallyNoetherian B]
  (e : CategoryTheory.EquivalenceRelation p q) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local instance stalkJacobianBoundary_affine : IsAffine J.subscheme :=
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

/-- Stalk differential generators at every associated test prime construct the full arrow. -/
theorem originalBoundary_lift_of_associated_stalk_jacobians
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Set.range t ⊆ Set.range c)
    (hfg : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      Module.Finite Γ(J.subscheme, ⊤) (KaehlerDifferential (Scalars f) Γ(J.subscheme, ⊤)))
    (hP : ∀ j, ∀ Q : PrimeSpectrum Γ(B.affineCover.X j, ⊤),
      Q.asIdeal ∈ associatedPrimes Γ(B.affineCover.X j, ⊤) Γ(B.affineCover.X j, ⊤) →
      ScalarStalkJacobianTests.Test s
        ((B.affineCover.f j ≫ t) ≫ pullback.snd f f).appTop.hom Q) :
    ∃! d : B ⟶ pullback p J.subschemeι, d ≫ c = t := by
  apply originalBoundary_unique_lift_of_affine_associated_differentials e J hJ t h
  intro j Q hQ
  exact ScalarStalkJacobianTests.exists_annihilator s
    ((B.affineCover.f j ≫ t) ≫ pullback.snd f f).appTop.hom
    ⟨Q, hQ.isPrime⟩ hfg (hP j ⟨Q, hQ.isPrime⟩ hQ)

section Rank
variable [IsSeparated p] [QuasiCompact p] [LocallyQuasiFinite p] [IsLocallyNoetherian A]
local instance stalkJacobianRankOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance stalkJacobianRankOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance stalkJacobianRankOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local irreducible] rankPullbackThickening rankPullbackMap
  rankThickening rankThickeningMap
variable (t : B ⟶ pullback
  (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))
  (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤))))
  (n k : ℕ)
local notation "S" => rankPullbackThickening (Over.mk p) (t ≫ x) n k
local notation "v" => rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t

/-- Local stalk generators and generic coverage give the whole nonreduced rank-stage arrow. -/
theorem originalBoundary_rankStage_lift_of_generic_stalk_jacobians
    (h : genericPoints S ⊆ v ⁻¹' Set.range c)
    (hfg : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      Module.Finite Γ(J.subscheme, ⊤) (KaehlerDifferential (Scalars f) Γ(J.subscheme, ⊤)))
    (hP : ∀ j, ∀ Q : PrimeSpectrum Γ((S).affineCover.X j, ⊤),
      Q.asIdeal ∈ associatedPrimes Γ((S).affineCover.X j, ⊤) Γ((S).affineCover.X j, ⊤) →
      ScalarStalkJacobianTests.Test s
        (((S).affineCover.f j ≫ v) ≫ pullback.snd f f).appTop.hom Q) :
    ∃! d : S ⟶ pullback p J.subschemeι, d ≫ c = v := by
  let _ : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian
    (rankPullbackMap (Over.mk p) (t ≫ x) n k)
  let _ := originalBoundary_rankStage_endpoint_finite J t n k
  exact originalBoundary_lift_of_associated_stalk_jacobians e J hJ v
    (originalBoundary_rankStage_coverage_of_generic J hJ t n k h) hfg hP

end Rank
end FLT.Mazur.EquivalenceRelationOrderedFrames
