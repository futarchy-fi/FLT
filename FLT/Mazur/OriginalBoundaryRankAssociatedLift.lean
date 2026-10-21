/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryAffineAssociatedLift
public import FLT.Mazur.OriginalBoundaryRankStageDenseCoverage

/-!
# Full nonreduced rank-stage arrows from generic coverage and associated rigidity

The full endpoint is finite by the original rank construction. Generic
component coverage propagates by closedness. Affine associated-prime lifts
then glue over the entire stage, retaining both original endpoint equations.
Generic coverage and associated rigidity remain explicit geometric inputs.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeScalarImageQuotient FlatScalarFunctionPushout
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem rank_associated_dense_of_generic {X : Scheme.{0}} {s : Set X}
    (h : genericPoints X ⊆ s) : Dense s := by
  have hd : Dense (genericPoints X) := by
    rw [dense_iff_closure_eq, genericPoints.closure]
  exact hd.mono h

variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsAffine A]
  [Etale p] [IsSeparated p] [QuasiCompact p] [LocallyQuasiFinite p]
  [IsLocallyNoetherian A] [IsLocallyNoetherian B]
  (e : CategoryTheory.EquivalenceRelation p q) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local instance rankAssociatedOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance rankAssociatedOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance rankAssociatedOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local instance rankAssociatedBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "s" => RingHom.kerLift (FlatScalarFunctionPushout.scalarMap f)
attribute [local irreducible] scalarMorphism
variable (t : B ⟶ pullback
  (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))
  (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤))))
  (n k : ℕ)
local notation "S" => rankPullbackThickening (Over.mk p) (t ≫ x) n k
local notation "v" => rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t

omit e [IsLocallyNoetherian A] [IsLocallyNoetherian B] in
/-- Generic points cover the whole fixed full rank stage by its constructed finite comparison. -/
theorem originalBoundary_rankStage_coverage_of_generic
    (h : genericPoints S ⊆ v ⁻¹' Set.range c) : Set.range v ⊆ Set.range c := by
  let _ := originalBoundary_rankStage_surjective_of_dense J hJ t n k
    (rank_associated_dense_of_generic h)
  rintro _ ⟨u, rfl⟩
  have hu : u ∈ Set.range (pullback.snd c v) := (pullback.snd c v).surjective u
  rwa [Scheme.Pullback.range_snd] at hu

include e

/-- All affine associated primes control a unique full arrow on the unsplit nonreduced stage. -/
theorem originalBoundary_rankStage_unique_lift_of_generic_associated
    (h : genericPoints S ⊆ v ⁻¹' Set.range c)
    (hA : ∀ i, ∀ P ∈ associatedPrimes Γ((S).affineCover.X i, ⊤) Γ((S).affineCover.X i, ⊤),
      ∃ a : Γ(J.subscheme, ⊤),
        (let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra;
          a ∈ Module.annihilator Γ(J.subscheme, ⊤)
            (KaehlerDifferential (Scalars f) Γ(J.subscheme, ⊤))) ∧
        (((S).affineCover.f i ≫ v) ≫ pullback.snd f f).appTop a ∉ P) :
    ∃! d : S ⟶ pullback p J.subschemeι, d ≫ c = v := by
  let _ : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian
    (rankPullbackMap (Over.mk p) (t ≫ x) n k)
  let _ := originalBoundary_rankStage_endpoint_finite J t n k
  exact originalBoundary_unique_lift_of_affine_associated_differentials e J hJ v
    (originalBoundary_rankStage_coverage_of_generic J hJ t n k h) hA

/-- Associated unramified endpoints construct the same full rank-stage arrow. -/
theorem originalBoundary_rankStage_unique_lift_of_generic_unramified
    (h : genericPoints S ⊆ v ⁻¹' Set.range c)
    (hft : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      Algebra.EssFiniteType (Scalars f) Γ(J.subscheme, ⊤))
    (hU : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      ∀ i, ∀ P : PrimeSpectrum Γ((S).affineCover.X i, ⊤),
        P.asIdeal ∈ associatedPrimes Γ((S).affineCover.X i, ⊤) Γ((S).affineCover.X i, ⊤) →
        PrimeSpectrum.comap (((S).affineCover.f i ≫ v) ≫ pullback.snd f f).appTop.hom P ∈
          Algebra.unramifiedLocus (Scalars f) Γ(J.subscheme, ⊤)) :
    ∃! d : S ⟶ pullback p J.subschemeι, d ≫ c = v := by
  let _ : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian
    (rankPullbackMap (Over.mk p) (t ≫ x) n k)
  let _ := originalBoundary_rankStage_endpoint_finite J t n k
  exact originalBoundary_unique_lift_of_affine_associated_unramified e J hJ v
    (originalBoundary_rankStage_coverage_of_generic J hJ t n k h) hft hU

end FLT.Mazur.EquivalenceRelationOrderedFrames
