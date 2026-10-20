/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineLocallyFreeRelationTraceUnit
public import FLT.Mazur.FiniteProjectiveAffineNorm
public import FLT.Mazur.FiniteFlatGlobalSections
public import FLT.Mazur.InvariantIdealEquivalence

/-!
# Boundary invariant lifting for an entire finite etale affine relation

Finite projectivity constructs all trace charts. No supplied basis, rank
inversion or reducedness is required. The invariant boundary ideal can retain
arbitrary infinitesimal equations.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineFiniteEtaleBoundarySurjectivity
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {D A S : Scheme.{0}} [IsAffine A] [IsAffine S]
  (p q : D ⟶ A) (f : A ⟶ S) (h : p ≫ f = q ≫ f)
  (e : CategoryTheory.EquivalenceRelation p q) [IsFinite p] [Etale p] [IsSeparated f]
  {D' A' : Scheme.{0}} [IsAffine A']
  (p' q' : D' ⟶ A') (a : A' ⟶ A) (b : D' ⟶ D)
  (H : IsPullback b p' p a) (hq : b ≫ q = q' ≫ a)

include h e in
/-- All trace charts and the boundary invariant lift come from finite etale geometry. -/
theorem boundary_invariant_surjective [IsClosedImmersion a] :
    Function.Surjective
      (SchemeRelationInvariantSpectrum.relationPullback p q p' q' a b H.w hq) := by
  let _ : IsAffine D := isAffine_of_isAffineHom p
  let _ : IsFinite p' := MorphismProperty.of_isPullback H (inferInstanceAs (IsFinite p))
  let _ : IsAffine D' := isAffine_of_isAffineHom p'
  let _ := p.appTop.hom.toAlgebra
  let hf := p.finite_appTop
  let hp := FCurve.finiteFlat_appTop_projective p
  exact AffineLocallyFreeRelationTraceUnit.boundary_invariant_surjective p q f h e
    (FiniteProjectiveAffineNorm.chart p hf hp)
    (FiniteProjectiveAffineNorm.chart_basis p hf hp)
    (FiniteProjectiveAffineNorm.chart_cover p hf hp) p' q' a b H hq

variable (I : A.IdealSheafData) (hI : I.comap p = I.comap q)

include h e in
/-- Every invariant section on the actual closed ideal subscheme has an invariant lift. -/
theorem ideal_invariant_surjective : Function.Surjective
    (SchemeRelationInvariantSpectrum.relationPullback p q
      (pullback.snd p I.subschemeι) (InvariantIdealRelation.snd I p q hI)
      I.subschemeι (pullback.fst p I.subschemeι) pullback.condition
      (InvariantIdealRelation.snd_ι I p q hI).symm) := by
  let _ : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  exact boundary_invariant_surjective p q f h e _ _ _ _
    (IsPullback.of_hasPullback p I.subschemeι) (InvariantIdealRelation.snd_ι I p q hI).symm

end FLT.Mazur.AffineFiniteEtaleBoundarySurjectivity
