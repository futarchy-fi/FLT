/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryBranchScalars
public import FLT.Mazur.OriginalBoundaryResidualGeometricCover

/-!
# Residual coverage by full geometric boundary scalar equations

A scalar solution on each required full branch boundary constructs its own
invariant source numerator. Prime coverage and the literal boundary scalar
equation remain explicit; no reduced-fiber or single-component test suffices.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections SchemeOpenEnvelope SchemeScalarPrincipalNeighborhood
open RingPairInvariantFlatScalars FlatScalarSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A Z : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [IsAffine A] (e : CategoryTheory.EquivalenceRelation p q)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine Z] (f : A ⟶ Z) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (t : compatibleFunctions (pullback.snd p J.subschemeι)
    (InvariantIdealRelation.snd J p q hJ))
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "σ" => Subring.subtype (compatibleFunctions p q)
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
variable {ι : Type*} (S : ι → Type) [∀ i, CommRing (S i)]
  [∀ i, Algebra (invariants p.appTop.hom q.appTop.hom) (S i)]
  [∀ i, Module.Flat (invariants p.appTop.hom q.appTop.hom) (S i)]
  (Q : Ideal (compatibleFunctions p q))


include e hf in
/-- Full boundary scalar equations construct the required original residual multipliers. -/
theorem originalBoundaryLift_support_of_residual_scalar_cover
  (hbranch : ∀ x : PrimeSpectrum (compatibleFunctions p q),
    x ∈ closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (J.support : Set A)) ∩
      closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (finiteTargetOpen p : Set A)ᶜ) →
    x ∉ PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) →
    ∃ (i : ι) (P : PrimeSpectrum (S i)) (s : S i),
      P.asIdeal.comap (algebraMap (invariants p.appTop.hom q.appTop.hom) (S i)) = x.asIdeal ∧
      FlatScalarFunctionPushout.scalarMap (base R (S i) J.subscheme) s =
        (source R (S i) J.subscheme).appTop t.val) :
    PrimeSpectrum.zeroLocus
        (originalBoundaryLiftIdeal (p := p) (q := q) J t.val :
          Set (compatibleFunctions p q)) ⊆
      PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) := by
  apply originalBoundaryLift_support_of_residual_geometric_cover e J hJ f hf t S Q
  intro x hx hxQ
  obtain ⟨i, P, s, hP, hs⟩ := hbranch x hx hxQ
  obtain ⟨a, he, hb⟩ := originalBranch_lift_of_scalar p q (S i) J t.val s hs
  exact ⟨i, P, a, hP, he, hb⟩

include e hf in
/-- Finite generation of the specified ideal alone gives one power of original lift multipliers. -/
theorem exists_pow_le_originalBoundaryLiftIdeal_of_scalar_cover
  (hbranch : ∀ x : PrimeSpectrum (compatibleFunctions p q),
    x ∈ closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (J.support : Set A)) ∩
      closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (finiteTargetOpen p : Set A)ᶜ) →
    x ∉ PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) →
    ∃ (i : ι) (P : PrimeSpectrum (S i)) (s : S i),
      P.asIdeal.comap (algebraMap (invariants p.appTop.hom q.appTop.hom) (S i)) = x.asIdeal ∧
      FlatScalarFunctionPushout.scalarMap (base R (S i) J.subscheme) s =
        (source R (S i) J.subscheme).appTop t.val) (hfg : Q.FG) :
    ∃ N : ℕ, Q ^ N ≤ originalBoundaryLiftIdeal (p := p) (q := q) J t.val := by
  exact Ideal.exists_pow_le_of_le_radical_of_fg
    ((PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp
      (originalBoundaryLift_support_of_residual_scalar_cover e J hJ f hf t S Q hbranch)) hfg

end FLT.Mazur.EquivalenceRelationOrderedFrames
