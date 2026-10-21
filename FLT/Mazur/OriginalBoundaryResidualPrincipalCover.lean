/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryPrincipalLiftCriterion
public import FLT.Mazur.OriginalBoundaryResidualIdeal

/-!
# Lifting from a principal cover of the original residual intersection

Only primes in both closed bad images need further neighborhoods. A local
full boundary lift on such a neighborhood removes that prime from the exact
original obstruction support. This retains every original scalar prime and
the entire unreduced boundary; no rank correction is reversed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections SchemeOpenEnvelope SchemeScalarPrincipalNeighborhood
open InvariantOpenCoefficientRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [IsAffine A] (e : CategoryTheory.EquivalenceRelation p q)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (t : compatibleFunctions (pullback.snd p J.subschemeι)
    (InvariantIdealRelation.snd J p q hJ))
local notation "σ" => Subring.subtype (compatibleFunctions p q)

include e hf in
/-- Additional principal lifts need be constructed only on the residual intersection off V(Q). -/
theorem originalBoundaryLift_support_of_residual_principal_cover
    (Q : Ideal (compatibleFunctions p q))
    (hlocal : ∀ x : PrimeSpectrum (compatibleFunctions p q),
      x ∈ closure (scalarMorphism σ '' (J.support : Set A)) ∩
        closure (scalarMorphism σ '' (finiteTargetOpen p : Set A)ᶜ) →
      x ∉ PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) →
      ∃ (r : compatibleFunctions p q), r ∉ x.asIdeal ∧
        ∃ u : coefficients p q (A.basicOpen r.val) (compatibleFunctions_basicOpen p q r),
          (J.comap (A.basicOpen r.val).ι).subschemeι.appTop u.val =
            (IdealSheafClosedTransitions.map (J.comap (A.basicOpen r.val).ι) J
              (A.basicOpen r.val).ι rfl).appTop t.val) :
    PrimeSpectrum.zeroLocus
        (originalBoundaryLiftIdeal (p := p) (q := q) J t.val :
          Set (compatibleFunctions p q)) ⊆
      PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) := by
  let _ := QuasiCompact.compactSpace_of_compactSpace p
  let _ := quasiSeparatedSpace_of_quasiSeparated p
  intro x hx
  by_contra hxQ
  obtain ⟨r, hr, u, hu⟩ := hlocal x
    (originalBoundaryLift_support_subset_boundary_nonfinite e J hJ f hf t hx) hxQ
  obtain ⟨N, hN⟩ := exists_pow_mem_originalBoundaryLiftIdeal J t.val r u hu
  exact hr (x.isPrime.mem_of_pow_mem N (hx hN))

include e hf in
/-- Covering the residual intersection constructs a genuine original global invariant lift. -/
theorem exists_originalBoundaryLift_of_residual_principal_cover
    (hlocal : ∀ x : PrimeSpectrum (compatibleFunctions p q),
      x ∈ closure (scalarMorphism σ '' (J.support : Set A)) ∩
        closure (scalarMorphism σ '' (finiteTargetOpen p : Set A)ᶜ) →
      ∃ (r : compatibleFunctions p q), r ∉ x.asIdeal ∧
        ∃ u : coefficients p q (A.basicOpen r.val) (compatibleFunctions_basicOpen p q r),
          (J.comap (A.basicOpen r.val).ι).subschemeι.appTop u.val =
            (IdealSheafClosedTransitions.map (J.comap (A.basicOpen r.val).ι) J
              (A.basicOpen r.val).ι rfl).appTop t.val) :
    ∃ w : compatibleFunctions p q, J.subschemeι.appTop w.val = t.val := by
  have hz := originalBoundaryLift_support_of_residual_principal_cover e J hJ f hf t ⊤
    (fun x hx _ ↦ hlocal x hx)
  simp only [Submodule.top_coe, PrimeSpectrum.zeroLocus_univ] at hz
  apply (one_mem_originalBoundaryLiftIdeal J t.val).mp
  rw [PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp (Set.eq_empty_of_subset_empty hz)]
  trivial

end FLT.Mazur.EquivalenceRelationOrderedFrames
