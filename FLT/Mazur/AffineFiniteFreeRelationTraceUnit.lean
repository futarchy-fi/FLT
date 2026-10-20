/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EndpointTraceIdealDescent
public import FLT.Mazur.FiniteRelationEndpointSpan
public import FLT.Mazur.AffineEtaleTraceSurjectivity
public import FLT.Mazur.AffineTraceGlobalBasis
public import FLT.Mazur.AffineLocallyFreeBoundaryTrace
public import FLT.Mazur.AffineLocallyFreeIntegralCoordinates

/-!
# Unit generation for the entire finite free étale relation

The reflexivity section gives surjectivity of the full multiplication trace.
Closed endpoint spanning and integral invariant inclusion descend the unit
ideal to the unchanged invariant ring, for arbitrary local trace charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Module
namespace FLT.Mazur.AffineFiniteFreeRelationTraceUnit
open SchemeEffectiveEpiSections AffineLocallyFreeRelationTrace
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {D A S : Scheme.{u}} [IsAffine D] [IsAffine A] [IsAffine S]
  (p q : D ⟶ A) (f : A ⟶ S) (h : p ≫ f = q ≫ f)
  (e : CategoryTheory.EquivalenceRelation p q) [IsFinite p] [Etale p] [IsSeparated f]
  {κ : Type w} (U : κ → A.affineOpens)
  (hU : ∀ j, AffineOpenNorm.HasBasis p (U j)) (hcover : ⨆ j, (U j).1 = ⊤)
  {ι : Type v} [Finite ι]

include h in
/-- Actual full-relation traces generate one in the original invariant ring. -/
theorem invariantTraceIdeal_eq_top :
    let _ := p.appTop.hom.toAlgebra
    Basis ι Γ(A, ⊤) Γ(D, ⊤) →
      Ideal.span (Set.range (invariantTrace p q U hU hcover e)) = ⊤ := by
  let _ := p.appTop.hom.toAlgebra
  dsimp only
  intro basis
  apply EndpointTraceIdealDescent.traceIdeal_eq_top q.appTop
    (Algebra.trace Γ(A, ⊤) Γ(D, ⊤)) (compatibleFunctions p q).subtype
    Subtype.val_injective
    (AffineLocallyFreeRelationCharpoly.invariant_inclusion_integral p q U hU hcover e)
  · intro a
    exact AffineTraceGlobalBasis.trace_eq_sectionTrace p U hU hcover basis (q.appTop a)
  · exact FiniteRelationEndpointSpan.span_range_eq_top p q f h e
  · exact AffineEtaleTraceSurjectivity.sectionTrace_surjective p e.r e.reflexivity₁ basis

variable {D' A' : Scheme.{u}} [IsAffine D'] [IsAffine A']
  (p' q' : D' ⟶ A') (a : A' ⟶ A) (b : D' ⟶ D)
  (H : IsPullback b p' p a) (hq : b ≫ q = q' ≫ a)

include h e hU hcover in
/-- A cartesian closed boundary has surjective restriction on the original invariant rings. -/
theorem boundary_invariant_surjective [IsClosedImmersion a] :
    let _ := p.appTop.hom.toAlgebra
    Basis ι Γ(A, ⊤) Γ(D, ⊤) →
      Function.Surjective
        (SchemeRelationInvariantSpectrum.relationPullback p q p' q' a b H.w hq) := by
  let _ := p.appTop.hom.toAlgebra
  dsimp only
  intro basis t
  apply (sectionLiftIdeal_eq_top_iff _ t).mp
  apply top_unique
  rw [← invariantTraceIdeal_eq_top p q f h e U hU hcover basis]
  apply Ideal.span_le.mpr
  rintro _ ⟨s, rfl⟩
  exact invariantTrace_mem_sectionLiftIdeal p q U hU hcover e p' q' a b H hq
    (IsClosedImmersion.isAffine_surjective_of_isAffine a).2 t s

end FLT.Mazur.AffineFiniteFreeRelationTraceUnit
