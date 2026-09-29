/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCohomologyVanishingCechSequence
public import FLT.Mazur.AffineCohomologyVanishingRelDescent
public import FLT.Mazur.AffineCohomologyVanishingRelInjective

/-!
# The cofinal principal-cover criterion

Positive Cech exactness for every finite principal cover of every principal open
implies positive Ext cohomology vanishing. The criterion passes to the cokernel
of an injective embedding by section descent and the Cech homology sequence.
All coefficients in the induction are arbitrary abelian sheaves.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace FLT.Mazur.AffineCohomologyVanishingCofinal

open CechSheafHZero CechFreeOpen CechConnecting CechAcyclicComparison
open AffineCohomologyVanishingLocal AffineCohomologyVanishingRelDescent
open AffineCohomologyVanishingRelInjective AffineCohomologyVanishingCechSequence

variable {R : CommRingCat.{u}}

/-- Positive Cech exactness for all finite principal covers of principal opens. -/
def PrincipalCoverExact (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (Spec R))) : Prop :=
  ∀ (r : R) (ι : Type u) (_ : Finite ι) (f : ι → R),
    (⨆ i, PrimeSpectrum.basicOpen (f i)) = PrimeSpectrum.basicOpen r →
    ∀ q : ℕ,
      (C (X := TopCat.of (Spec R)) (fun i ↦ PrimeSpectrum.basicOpen (f i)) F).ExactAt (q + 1)

/-- The criterion supplies the section lifts needed in every dimension shift. -/
lemma sections_surjective
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (Spec R)))}
    (hS : S.ShortExact) (hF : PrincipalCoverExact (R := R) S.X₁) (r : R) :
    Function.Surjective (S.g.hom.app (op (PrimeSpectrum.basicOpen r))) := by
  apply sections_surjective_on_basicOpen (R := R) hS r
  intro s hs
  exact hF r s inferInstance (fun f ↦ (f : R)) hs 0

/-- Section lifts on basic opens also lift on all Cech intersections. -/
lemma principal_cech_shortExact
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (Spec R)))}
    (hS : S.ShortExact) (hF : PrincipalCoverExact (R := R) S.X₁)
    {ι : Type u} (f : ι → R) :
    (cechShortComplex (fun i ↦ PrimeSpectrum.basicOpen (f i)) S).ShortExact := by
  apply cechShortComplex_shortExact_of_sections _ hS
  intro n a
  have h := sections_surjective (R := R) hS hF (∏ j, f (a j))
  rw [TildePrincipalOpen.cechTerm_open f n a] at h
  exact h

set_option maxHeartbeats 800000 in
-- Elaborating the bundled sheaf and Ext comparisons requires additional reduction.
/-- The criterion is stable under taking the cokernel of an injective embedding. -/
lemma principalCoverExact_cokernel
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (Spec R)))}
    (hS : S.ShortExact) [Injective S.X₂] (hF : PrincipalCoverExact (R := R) S.X₁) :
    PrincipalCoverExact (R := R) S.X₃ := by
  intro r ι hι f hf q
  let U : ι → Opens (TopCat.of (Spec R)) := fun i ↦ PrimeSpectrum.basicOpen (f i)
  have hC := principal_cech_shortExact (R := R) hS hF f
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hC.homology_exact₃ (q + 1) (q + 2) rfl).isZero_X₂
    ((cech_exactAt_of_injective_relative U S.X₂ q).isZero_homology.eq_of_src _ _)
    ((hF r ι hι f hf (q + 1)).isZero_homology.eq_of_tgt _ _)

/-- Each chosen quotient inherits the same concrete principal-cover criterion. -/
lemma embeddingSequence_principalCoverExact
    (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (Spec R)))
    (hF : PrincipalCoverExact (R := R) F) : PrincipalCoverExact (R := R) (embeddingSequence F).X₃ :=
  principalCoverExact_cokernel (R := R) (embeddingSequence_shortExact F) hF

variable [HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology (TopCat.of (Spec R))) AddCommGrpCat.{u})]

local instance cofinalHasExt :
    HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (Spec R))) :=
  inferInstanceAs (HasExt.{u + 1}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (Spec R))) AddCommGrpCat.{u}))

/-- Section surjectivity is degree-zero Ext surjectivity on a principal open. -/
lemma hPrime_zero_surjective
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (Spec R)))}
    (hS : S.ShortExact) (hF : PrincipalCoverExact (R := R) S.X₁) (r : R)
    (b : S.X₃.H' 0 (PrimeSpectrum.basicOpen r)) :
    ∃ a : S.X₂.H' 0 (PrimeSpectrum.basicOpen r),
      a.comp (Abelian.Ext.mk₀ S.g) (add_zero 0) = b := by
  let W := PrimeSpectrum.basicOpen r
  obtain ⟨t, ht⟩ := sections_surjective (R := R) hS hF r (hPrimeZeroEquiv W S.X₃ b)
  refine ⟨(hPrimeZeroEquiv W S.X₂).symm t, ?_⟩
  apply (hPrimeZeroEquiv W S.X₃).injective
  change hPrimeZeroEquiv W S.X₃
    (((Sheaf.cohomologyPresheafFunctor _ 0).map S.g).app (op W)
      ((hPrimeZeroEquiv W S.X₂).symm t)) = _
  rw [hPrimeZeroEquiv_naturality, AddEquiv.apply_symm_apply, ht]

set_option maxHeartbeats 800000 in
-- Elaborating the bundled sheaf and Ext comparisons requires additional reduction.
/-- First Ext cohomology on every principal open vanishes by section descent. -/
lemma hPrime_one_subsingleton
    (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (Spec R)))
    (hF : PrincipalCoverExact (R := R) F) (r : R) :
    Subsingleton (F.H' 1 (PrimeSpectrum.basicOpen r)) := by
  let S := embeddingSequence F
  have hS := embeddingSequence_shortExact F
  apply subsingleton_of_forall_eq 0
  intro a
  obtain ⟨b, hb⟩ := Abelian.Ext.covariant_sequence_exact₁
    (freeOpen (X := TopCat.of (Spec R)) (PrimeSpectrum.basicOpen r)) hS a
    (Abelian.Ext.eq_zero_of_injective _) (n₀ := 0) rfl
  obtain ⟨c, hc⟩ := hPrime_zero_surjective (R := R) hS hF r b
  rw [← hb, ← hc, Abelian.Ext.comp_assoc_of_second_deg_zero,
    ShortComplex.ShortExact.comp_extClass, Abelian.Ext.comp_zero]

set_option maxHeartbeats 800000 in
-- Elaborating the bundled sheaf and Ext comparisons requires additional reduction.
/-- All positive Ext degrees vanish on every principal open under the criterion. -/
theorem hPrime_succ_subsingleton (q : ℕ)
    (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (Spec R)))
    (hF : PrincipalCoverExact (R := R) F) (r : R) :
    Subsingleton (F.H' (q + 1) (PrimeSpectrum.basicOpen r)) := by
  induction q generalizing F with
  | zero => exact hPrime_one_subsingleton (R := R) F hF r
  | succ q ih =>
    let S := embeddingSequence F
    have hS := embeddingSequence_shortExact F
    have hQ := ih S.X₃ (embeddingSequence_principalCoverExact (R := R) F hF)
    apply subsingleton_of_forall_eq 0
    intro a
    obtain ⟨b, hb⟩ := Abelian.Ext.covariant_sequence_exact₁
      (freeOpen (X := TopCat.of (Spec R)) (PrimeSpectrum.basicOpen r)) hS a
      (Abelian.Ext.eq_zero_of_injective _) (n₀ := q + 1) rfl
    rw [← hb, hQ.elim b 0, Abelian.Ext.zero_comp]

/-- The all-degree cofinal-cover criterion for actual global sheaf cohomology. -/
theorem sheafH_succ_subsingleton
    (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (Spec R)))
    (hF : PrincipalCoverExact (R := R) F) (q : ℕ) : Subsingleton (Sheaf.H F (q + 1)) := by
  have h := hPrime_succ_subsingleton (R := R) q F hF 1
  rw [PrimeSpectrum.basicOpen_one] at h
  exact (sheafHTopEquiv F (q + 1)).injective.subsingleton

end FLT.Mazur.AffineCohomologyVanishingCofinal
