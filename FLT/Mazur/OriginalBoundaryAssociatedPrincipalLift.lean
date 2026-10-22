/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AssociatedPrincipalClosedImmersion
public import FLT.Mazur.OriginalBoundaryUnramifiedOpenLift
public import FLT.Mazur.ScalarSourceOpenRigidity

/-!
# Full original arrows from associated principal rigidity neighborhoods

Each associated prime may use its own formally unramified source principal
open. No global differential finiteness or global annihilator is required.
Closed-immersion detection retains the entire nonreduced test scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeScalarImageQuotient FlatScalarFunctionPushout
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem finite_endpoint_precompose {D A B V : Scheme.{0}}
    (p : D ⟶ A) (b : B ⟶ A) (v : V ⟶ B) [IsFinite (pullback.snd p b)] :
    IsFinite (pullback.snd p (v ≫ b)) := by
  rw [← pullbackLeftPullbackSndIso_inv_snd_snd p b v]
  infer_instance

private theorem principal_endpoint_range {B X : Scheme.{0}} (y : B ⟶ X) (a : Γ(X, ⊤)) :
    Set.range ((B.basicOpen (y.appTop a)).ι ≫ y) ⊆ X.basicOpen a := by
  rintro _ ⟨v, rfl⟩
  change v.val ∈ y ⁻¹ᵁ X.basicOpen a
  simpa only [Scheme.preimage_basicOpen_top] using v.property

private theorem principal_coverage_dense {C T B V : Scheme.{0}}
    (c : C ⟶ T) (t : B ⟶ T) (v : V ⟶ B) (h : Set.range t ⊆ Set.range c) :
    Dense ((v ≫ t) ⁻¹' Set.range c) := by
  have he : (v ≫ t) ⁻¹' Set.range c = Set.univ :=
    Set.eq_univ_of_forall (fun u ↦ h (Set.mem_range_self (v u)))
  rw [he]
  exact dense_univ

variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsAffine A] [Etale p]
  [IsAffine B] [IsNoetherian B]
  (e : CategoryTheory.EquivalenceRelation p q) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local instance associatedPrincipalBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
local notation "x" => pullback.fst f f ≫ J.subschemeι
attribute [local irreducible] scalarMorphism

local notation "s" => RingHom.kerLift (FlatScalarFunctionPushout.scalarMap f)

include e

/-- Each principal rigidity neighborhood constructs an actual arrow on its test principal open. -/
theorem originalBoundary_rigidity_principal_lift
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Set.range t ⊆ Set.range c) (a : Γ(J.subscheme, ⊤))
    (ha : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      Algebra.FormallyUnramified (Scalars f) (Localization.Away a)) :
    ∃ d : (B.basicOpen ((t ≫ pullback.snd f f).appTop a)).toScheme ⟶
      pullback p J.subschemeι,
      d ≫ c = (B.basicOpen ((t ≫ pullback.snd f f).appTop a)).ι ≫ t := by
  let U := J.subscheme.basicOpen a
  let V := B.basicOpen ((t ≫ pullback.snd f f).appTop a)
  let _ : IsAffine V.toScheme := inferInstance
  let _ := isLocallyNoetherian_of_isOpenImmersion V.ι
  let _ : IsNoetherian V.toScheme := ⟨⟩
  let _ : FormallyUnramified (U.ι ≫ projection f) :=
    ScalarDifferentialPrincipalRigidity.principal_formallyUnramified_of_away s a ha
  let _ : IsFinite (pullback.snd p ((V.ι ≫ t) ≫ x)) := by
    rw [Category.assoc]
    exact finite_endpoint_precompose p (t ≫ x) V.ι
  apply (originalBoundary_full_lift_of_unramified_open e J hJ U (V.ι ≫ t)
    (principal_coverage_dense c t V.ι h) _).exists
  simpa only [Category.assoc] using principal_endpoint_range (t ≫ pullback.snd f f) a

/-- Rigidity at associated test primes kills the entire finite comparison obstruction. -/
theorem originalBoundary_comparison_isIso_of_associated_principals
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Set.range t ⊆ Set.range c)
    (hA : ∀ P ∈ associatedPrimes Γ(B, ⊤) Γ(B, ⊤),
      ∃ a : Γ(J.subscheme, ⊤),
        (let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra;
          Algebra.FormallyUnramified (Scalars f) (Localization.Away a)) ∧
        (t ≫ pullback.snd f f).appTop a ∉ P) : IsIso (pullback.snd c t) := by
  let _ := IsLocallyNoetherian.component_noetherian
    (⟨⊤, isAffineOpen_top B⟩ : B.affineOpens)
  let _ := originalBoundary_comparison_test_closedImmersion J hJ t e
  let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
  apply AssociatedPrincipalClosedImmersion.isIso_of_associated_sections
  intro P hP
  obtain ⟨a, ha, hPa⟩ := hA P hP
  obtain ⟨d, hd⟩ := originalBoundary_rigidity_principal_lift e J hJ t h a ha
  exact ⟨(t ≫ pullback.snd f f).appTop a, hPa,
    pullback.lift d (B.basicOpen ((t ≫ pullback.snd f f).appTop a)).ι hd,
    pullback.lift_snd _ _ _⟩

/-- The unique full original arrow is constructed on the entire nonreduced test. -/
theorem originalBoundary_unique_lift_of_associated_principals
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Set.range t ⊆ Set.range c)
    (hA : ∀ P ∈ associatedPrimes Γ(B, ⊤) Γ(B, ⊤),
      ∃ a : Γ(J.subscheme, ⊤),
        (let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra;
          Algebra.FormallyUnramified (Scalars f) (Localization.Away a)) ∧
        (t ≫ pullback.snd f f).appTop a ∉ P) :
    ∃! d : B ⟶ pullback p J.subschemeι, d ≫ c = t := by
  let _ := originalBoundary_comparison_isIso_of_associated_principals e J hJ t h hA
  let _ := originalBoundaryComparison_mono e J hJ
  refine ⟨inv (pullback.snd c t) ≫ pullback.fst c t, ?_, ?_⟩
  · change (inv (pullback.snd c t) ≫ pullback.fst c t) ≫ c = t
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  · intro d hd
    apply (cancel_mono c).mp
    rw [hd, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

end FLT.Mazur.EquivalenceRelationOrderedFrames
