/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteEtalePullbackNilpotentLift
public import FLT.Mazur.OriginalBoundaryFiniteComparisonTests
public import FLT.Mazur.SchemeDenseComparisonNilpotentThickening

/-!
# Original first-endpoint lifts over nonreduced coefficient schemes

Dense comparison coverage, one full finite endpoint, and Noetherian affine
coefficients construct an actual original arrow across the comparison
thickening. Its first endpoint is exact on the full coefficient scheme. The
second endpoint is exact on the comparison thickening; extending that equation
to the whole coefficient scheme remains a separate infinitesimal obligation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeFiniteEndpointComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsAffine A] [Etale p]
  [IsAffine B] [IsNoetherian B]
  (e : CategoryTheory.EquivalenceRelation p q) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local instance nilpotentEndpointBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
local notation "x" => pullback.fst f f ≫ J.subschemeι
attribute [local irreducible] scalarMorphism

include e

/-- A unique full original source arrow extends the comparison with its first endpoint fixed. -/
theorem originalBoundary_nilpotent_ambient_lift
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Dense (t ⁻¹' Set.range c)) :
    ∃! d : B ⟶ D,
      pullback.snd c t ≫ d = pullback.fst c t ≫ pullback.fst p J.subschemeι ∧
      d ≫ p = t ≫ x := by
  let _ := originalBoundary_comparison_test_closedImmersion J hJ t e
  have hn := comparison_kernel_sheaf_isNilpotent_of_dense c t h
  apply FiniteEtalePullbackNilpotentLift.existsUnique_lift (pullback.snd c t) hn p
    (pullback.fst c t ≫ pullback.fst p J.subschemeι) (t ≫ x)
  have hc : c ≫ x = pullback.fst p J.subschemeι ≫ p := by
    simp only [originalBoundaryComparison, pullback.lift_fst_assoc, pullback.condition]
  rw [Category.assoc, ← hc, ← Category.assoc, pullback.condition, Category.assoc]

/-- The constructed arrow lies in the unchanged original boundary on the entire thickening. -/
theorem originalBoundary_nilpotent_boundary_lift
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Dense (t ⁻¹' Set.range c)) :
    ∃ d : B ⟶ pullback p J.subschemeι,
      d ≫ pullback.snd p J.subschemeι = t ≫ pullback.fst f f ∧
      pullback.snd c t ≫ d = pullback.fst c t := by
  obtain ⟨d, hd, _⟩ := originalBoundary_nilpotent_ambient_lift e J hJ t h
  have hp : d ≫ p = (t ≫ pullback.fst f f) ≫ J.subschemeι := by
    rw [Category.assoc]
    exact hd.2
  refine ⟨pullback.lift d (t ≫ pullback.fst f f) hp, pullback.lift_snd _ _ _, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hd.1]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, ← pullback.condition,
      Category.assoc]
    simp only [originalBoundaryComparison, pullback.lift_fst]

/-- The actual second endpoint is preserved on the full comparison thickening. -/
theorem originalBoundary_nilpotent_endpoint_equations
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Dense (t ⁻¹' Set.range c)) :
    ∃ d : B ⟶ pullback p J.subschemeι,
      d ≫ pullback.snd p J.subschemeι = t ≫ pullback.fst f f ∧
      pullback.snd c t ≫ (d ≫ InvariantIdealRelation.snd J p q hJ) =
        pullback.snd c t ≫ (t ≫ pullback.snd f f) := by
  obtain ⟨d, hd, hi⟩ := originalBoundary_nilpotent_boundary_lift e J hJ t h
  refine ⟨d, hd, ?_⟩
  rw [← Category.assoc, hi, ← Category.assoc, ← pullback.condition, Category.assoc]
  simp only [originalBoundaryComparison, pullback.lift_snd]

end FLT.Mazur.EquivalenceRelationOrderedFrames
