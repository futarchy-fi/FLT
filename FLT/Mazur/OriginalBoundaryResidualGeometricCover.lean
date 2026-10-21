/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryGeometricTensor
public import FLT.Mazur.OriginalBoundaryResidualTensorCover

/-!
# Residual support from actual full geometric branch functions

The three coefficient comparisons and independent endpoint squares are
constructed on the canonical base change over the original invariant ring.
Only the existence and coverage of actual branch solutions remain hypotheses.
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
/-- Actual geometric branch solutions remove each required residual original scalar prime. -/
theorem originalBoundaryLift_support_of_residual_geometric_cover
  (hbranch : ∀ x : PrimeSpectrum (compatibleFunctions p q),
    x ∈ closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (J.support : Set A)) ∩
      closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (finiteTargetOpen p : Set A)ᶜ) →
    x ∉ PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) →
    ∃ (i : ι) (P : PrimeSpectrum (S i)) (a : Γ(baseChange R (S i) A, ⊤)),
      P.asIdeal.comap (algebraMap (invariants p.appTop.hom q.appTop.hom) (S i)) = x.asIdeal ∧
      (originalBranchFirst p q (S i)).appTop a = (originalBranchSecond p q (S i)).appTop a ∧
      (originalBranchBoundary p q J (S i)).appTop a =
        (source R (S i) J.subscheme).appTop t.val) :
    PrimeSpectrum.zeroLocus
        (originalBoundaryLiftIdeal (p := p) (q := q) J t.val :
          Set (compatibleFunctions p q)) ⊆
      PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) := by
  let _ : CompactSpace D := QuasiCompact.compactSpace_of_compactSpace p
  let _ : QuasiSeparatedSpace D := quasiSeparatedSpace_of_quasiSeparated p
  let _ : CompactSpace J.subscheme := QuasiCompact.compactSpace_of_compactSpace J.subschemeι
  let _ : QuasiSeparatedSpace J.subscheme := quasiSeparatedSpace_of_quasiSeparated J.subschemeι
  apply originalBoundaryLift_support_of_residual_tensor_cover e J hJ f hf t S Q
  intro x hx hxQ
  obtain ⟨i, P, a, hP, he, hb⟩ := hbranch x hx hxQ
  obtain ⟨z, hz, hzb⟩ :=
    (originalBoundary_tensor_lift_iff_geometric p q J (S i) t.val).mpr ⟨a, he, hb⟩
  exact ⟨i, P, z, hP, hz, hzb⟩

include e hf in
/-- Finite generation of the specified ideal alone gives one power of original lift multipliers. -/
theorem exists_pow_le_originalBoundaryLiftIdeal_of_geometric_cover
  (hbranch : ∀ x : PrimeSpectrum (compatibleFunctions p q),
    x ∈ closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (J.support : Set A)) ∩
      closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (finiteTargetOpen p : Set A)ᶜ) →
    x ∉ PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) →
    ∃ (i : ι) (P : PrimeSpectrum (S i)) (a : Γ(baseChange R (S i) A, ⊤)),
      P.asIdeal.comap (algebraMap (invariants p.appTop.hom q.appTop.hom) (S i)) = x.asIdeal ∧
      (originalBranchFirst p q (S i)).appTop a = (originalBranchSecond p q (S i)).appTop a ∧
      (originalBranchBoundary p q J (S i)).appTop a =
        (source R (S i) J.subscheme).appTop t.val) (hfg : Q.FG) :
    ∃ N : ℕ, Q ^ N ≤ originalBoundaryLiftIdeal (p := p) (q := q) J t.val := by
  exact Ideal.exists_pow_le_of_le_radical_of_fg
    ((PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp
      (originalBoundaryLift_support_of_residual_geometric_cover e J hJ f hf t S Q hbranch)) hfg

end FLT.Mazur.EquivalenceRelationOrderedFrames
