/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryComparisonClosedImage
public import FLT.Mazur.SchemeFiniteEndpointComparison

/-!
# Full finite endpoint tests close the actual original comparison

The whole original comparison pulls back to a finite closed immersion when
its first full endpoint source is finite. Its actual image therefore survives
specialization. Over a domain, generic image membership covers every point of
the entire coefficient spectrum, without choosing a generic arrow over its
fraction field or replacing the original boundary by its reduction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeFiniteEndpointComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsAffine A]
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
local instance finiteComparisonBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
local notation "x" => pullback.fst f f ≫ J.subschemeι
attribute [local irreducible] scalarMorphism

omit [IsAffine A] in
private theorem comparison_endpoint_finite
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))] :
    IsFinite (pullback.snd (c ≫ x) (t ≫ x)) := by
  have hc : c ≫ x = pullback.fst p J.subschemeι ≫ p := by
    simp only [originalBoundaryComparison, pullback.lift_fst_assoc, pullback.condition]
  rw [hc]
  exact finite_pullback_precomp (pullback.fst p J.subschemeι) p (t ≫ x)

/-- The full comparison over the coefficient test is finite, with no image geometry hypothesis. -/
theorem originalBoundary_comparison_test_finite
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))] :
    IsFinite (pullback.snd c t) := by
  let _ := comparison_endpoint_finite J hJ t
  exact finite_pullback_of_finite_endpoint c x t

/-- The original equivalence relation makes this finite test an actual closed immersion. -/
theorem originalBoundary_comparison_test_closedImmersion
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (e : CategoryTheory.EquivalenceRelation p q) : IsClosedImmersion (pullback.snd c t) := by
  let _ := originalBoundaryComparison_mono e J hJ
  let _ := comparison_endpoint_finite J hJ t
  exact closedImmersion_pullback_of_finite_endpoint c x t

/-- Actual original comparison coverage extends along every specialization in this full test. -/
theorem originalBoundary_comparison_test_specializes
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    {u v : B} (huv : u ⤳ v)
    (hu : t u ∈ Set.range c) : t v ∈ Set.range c := by
  let _ := comparison_endpoint_finite J hJ t
  exact mem_range_of_specializes_of_finite_endpoint c x t huv hu

/-- Over any domain, generic coverage and one finite full endpoint cover the entire test. -/
theorem originalBoundary_comparison_test_coverage_of_generic {R : Type}
    [CommRing R] [IsDomain R] (a : Spec (.of R) ⟶ pullback f f)
    [IsFinite (pullback.snd p (a ≫ x))]
    (ha : a (⊥ : PrimeSpectrum R) ∈ Set.range c) : Set.range a ⊆ Set.range c := by
  rintro _ ⟨u, rfl⟩
  exact originalBoundary_comparison_test_specializes J hJ a
    ((PrimeSpectrum.le_iff_specializes _ _).mp bot_le) ha

end FLT.Mazur.EquivalenceRelationOrderedFrames
