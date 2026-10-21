/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryTensorLift
public import FLT.Mazur.OriginalBoundaryResidualIdeal

/-!
# Residual support from flat branch-only boundary numerators

Only the intersection of the two original bad-image closures is tested.
A full tensor invariant lifting the entire boundary at a point above each
required prime constructs an original multiplier. Neither an original raw
numerator nor finite generation of the invariant ring is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections SchemeOpenEnvelope SchemeScalarPrincipalNeighborhood
open RingPairInvariantFlatScalars FlatAlgebraEqualizer
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
local notation "α" => first p.appTop.hom q.appTop.hom
local notation "β" => second p.appTop.hom q.appTop.hom
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
variable {ι : Type*} (S : ι → Type) [∀ i, CommRing (S i)]
  [∀ i, Algebra (invariants p.appTop.hom q.appTop.hom) (S i)]
  [∀ i, Module.Flat (invariants p.appTop.hom q.appTop.hom) (S i)]
  (Q : Ideal (compatibleFunctions p q))


include e hf in
/-- Full branch-only solutions remove every required residual original scalar prime. -/
theorem originalBoundaryLift_support_of_residual_tensor_cover
  (hbranch : ∀ x : PrimeSpectrum (compatibleFunctions p q),
    x ∈ closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (J.support : Set A)) ∩
      closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (finiteTargetOpen p : Set A)ᶜ) →
    x ∉ PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) →
    ∃ (i : ι) (P : PrimeSpectrum (S i)) (a : S i ⊗[invariants p.appTop.hom q.appTop.hom] Γ(A, ⊤)),
      P.asIdeal.comap (algebraMap (invariants p.appTop.hom q.appTop.hom) (S i)) = x.asIdeal ∧
      tensorMap (S i) (first p.appTop.hom q.appTop.hom) a =
        tensorMap (S i) (second p.appTop.hom q.appTop.hom) a ∧
      tensorMap (S i) (originalBoundaryMap J) a = 1 ⊗ₜ[R] t.val) :
    PrimeSpectrum.zeroLocus
        (originalBoundaryLiftIdeal (p := p) (q := q) J t.val :
          Set (compatibleFunctions p q)) ⊆
      PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) := by
  intro x hx
  by_contra hxQ
  obtain ⟨i, P, a, hP, he, hb⟩ := hbranch x
    (originalBoundaryLift_support_subset_boundary_nonfinite e J hJ f hf t hx) hxQ
  obtain ⟨r, hr, hrt⟩ := exists_originalBoundaryLift_multiplier_of_tensor J (S i)
    P.asIdeal t.val 1 P.isPrime.one_notMem a he (by simpa only [map_one, one_mul] using hb)
  apply hr
  change r ∈ P.asIdeal.comap (algebraMap R (S i))
  rw [hP]
  exact hx hrt

include e hf in
/-- Finite generation of the specified ideal alone gives one power of original lift multipliers. -/
theorem exists_pow_le_originalBoundaryLiftIdeal_of_tensor_cover
  (hbranch : ∀ x : PrimeSpectrum (compatibleFunctions p q),
    x ∈ closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (J.support : Set A)) ∩
      closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (finiteTargetOpen p : Set A)ᶜ) →
    x ∉ PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) →
    ∃ (i : ι) (P : PrimeSpectrum (S i)) (a : S i ⊗[invariants p.appTop.hom q.appTop.hom] Γ(A, ⊤)),
      P.asIdeal.comap (algebraMap (invariants p.appTop.hom q.appTop.hom) (S i)) = x.asIdeal ∧
      tensorMap (S i) (first p.appTop.hom q.appTop.hom) a =
        tensorMap (S i) (second p.appTop.hom q.appTop.hom) a ∧
      tensorMap (S i) (originalBoundaryMap J) a = 1 ⊗ₜ[R] t.val) (hfg : Q.FG) :
    ∃ N : ℕ, Q ^ N ≤ originalBoundaryLiftIdeal (p := p) (q := q) J t.val := by
  exact Ideal.exists_pow_le_of_le_radical_of_fg
    ((PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp
      (originalBoundaryLift_support_of_residual_tensor_cover e J hJ f hf t S Q hbranch)) hfg

end FLT.Mazur.EquivalenceRelationOrderedFrames
