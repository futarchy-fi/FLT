/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryDifferentialOpenLift

/-!
# Differential-open arrows on arbitrary locally Noetherian tests

Affine lifts glue first on any prescribed unramified endpoint open. Actual
differential annihilators then construct such opens, and their union carries
a unique full original arrow. The test need not be affine or quasi-compact.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeScalarImageQuotient FlatScalarFunctionPushout
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem global_diff_finite_precompose {D A B V : Scheme.{0}}
    (p : D ⟶ A) (b : B ⟶ A) (v : V ⟶ B) [IsFinite (pullback.snd p b)] :
    IsFinite (pullback.snd p (v ≫ b)) := by
  rw [← pullbackLeftPullbackSndIso_inv_snd_snd p b v]
  infer_instance

private theorem global_diff_coverage_precompose {C T B V : Scheme.{0}}
    (c : C ⟶ T) (t : B ⟶ T) (v : V ⟶ B) (h : Set.range t ⊆ Set.range c) :
    Set.range (v ≫ t) ⊆ Set.range c := by
  rintro _ ⟨u, rfl⟩
  exact h (Set.mem_range_self (v u))

variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsAffine A] [Etale p]
  [IsLocallyNoetherian B]
  (e : CategoryTheory.EquivalenceRelation p q) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local instance globalDiffBoundary_affine : IsAffine J.subscheme :=
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

/-- Full local lifts glue without a compactness or affineness hypothesis on the test. -/
theorem originalBoundary_localNoetherian_lift_of_unramified_open
    (U : J.subscheme.Opens) [FormallyUnramified (U.ι ≫ projection f)]
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Set.range t ⊆ Set.range c)
    (hU : Set.range (t ≫ pullback.snd f f) ⊆ U) :
    ∃! d : B ⟶ pullback p J.subschemeι, d ≫ c = t := by
  let _ := originalBoundaryComparison_mono e J hJ
  apply MonoComparisonOpenGluing.existsUnique_of_cover c t B.affineCover
  intro i
  let _ : IsAffine (B.affineCover.X i) := isAffine_Spec _
  let _ := isLocallyNoetherian_of_isOpenImmersion (B.affineCover.f i)
  let _ : IsNoetherian (B.affineCover.X i) := ⟨⟩
  let _ : IsFinite (pullback.snd p ((B.affineCover.f i ≫ t) ≫ x)) := by
    rw [Category.assoc]
    exact global_diff_finite_precompose p (t ≫ x) (B.affineCover.f i)
  apply (originalBoundary_full_lift_of_unramified_open e J hJ U
    (B.affineCover.f i ≫ t) _ _).exists
  · have he : (B.affineCover.f i ≫ t) ⁻¹' Set.range c = Set.univ :=
      Set.eq_univ_of_forall (fun u ↦ h (Set.mem_range_self (B.affineCover.f i u)))
    rw [he]
    exact dense_univ
  · rintro _ ⟨u, rfl⟩
    exact hU (Set.mem_range_self (B.affineCover.f i u))

/-- A source differential annihilator constructs a full arrow on any test principal open. -/
theorem originalBoundary_localNoetherian_differential_principal_lift
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Set.range t ⊆ Set.range c) (a : Γ(J.subscheme, ⊤))
    (ha : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      a ∈ Module.annihilator Γ(J.subscheme, ⊤)
        (KaehlerDifferential (Scalars f) Γ(J.subscheme, ⊤))) :
    ∃! d : (B.basicOpen ((t ≫ pullback.snd f f).appTop a)).toScheme ⟶
      pullback p J.subschemeι,
      d ≫ c = (B.basicOpen ((t ≫ pullback.snd f f).appTop a)).ι ≫ t := by
  let U := J.subscheme.basicOpen a
  let V := B.basicOpen ((t ≫ pullback.snd f f).appTop a)
  let _ := isLocallyNoetherian_of_isOpenImmersion V.ι
  let _ : FormallyUnramified (U.ι ≫ projection f) :=
    ScalarDifferentialPrincipalRigidity.principal_formallyUnramified s a ha
  let _ : IsFinite (pullback.snd p ((V.ι ≫ t) ≫ x)) := by
    rw [Category.assoc]
    exact global_diff_finite_precompose p (t ≫ x) V.ι
  apply originalBoundary_localNoetherian_lift_of_unramified_open e J hJ U (V.ι ≫ t)
    (global_diff_coverage_precompose c t V.ι h)
  rintro _ ⟨v, rfl⟩
  change v.val ∈ (t ≫ pullback.snd f f) ⁻¹ᵁ U
  simpa only [U, V, Scheme.preimage_basicOpen_top] using v.property

/-- All differential principal arrows glue on the full test differential open. -/
theorem originalBoundary_localNoetherian_differentialOpen_lift
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Set.range t ⊆ Set.range c) :
    ∃! d : (originalBoundaryDifferentialOpen J t).toScheme ⟶ pullback p J.subschemeι,
      d ≫ c = (originalBoundaryDifferentialOpen J t).ι ≫ t := by
  let _ := originalBoundaryComparison_mono e J hJ
  apply PrincipalIdealComparisonLift.existsUnique_lift
  intro a ha
  exact (originalBoundary_localNoetherian_differential_principal_lift e J hJ t h a ha).exists

end FLT.Mazur.EquivalenceRelationOrderedFrames
