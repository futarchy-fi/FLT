/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteHopfFreeness
public import FLT.GroupScheme.FrobeniusCoordinateKernel
public import FLT.GroupScheme.FrobeniusSubalgebra
public import FLT.Mathlib.RingTheory.MvPolynomial.NilpotentPresentation

/-!
# Relative presentation over the Frobenius image

A finite local commutative Hopf algebra is presented over its Frobenius
subalgebra by one deformed pure-power equation per minimal coordinate.
This identifies the entire relative kernel. Passing from this relative
presentation to a minimal presentation over the field is a further step.
-/

@[expose] public noncomputable section

universe u

namespace HopfAlgebra

open MvPolynomial

variable {k A : Type u} [Field k] [CommRing A] [HopfAlgebra k A]
  [IsLocalRing A] [Module.Finite k A]
  (p : ℕ) [Fact p.Prime] [CharP k p] [CharP A p] [PerfectRing k p]

omit [IsLocalRing A] in
/-- A finite Hopf algebra is free over its Frobenius image. -/
theorem free_frobeniusImage : Module.Free (Algebra.frobeniusImage k A p 1) A := by
  let := frobeniusImageHopfAlgebra (k := k) (A := A) p 1
  exact free_of_injective_bialgHom (frobeniusImageInclusion (k := k) (A := A) p 1)
    rfl Subtype.val_injective

/-- Minimal coordinates give all relative relations over the Frobenius
subalgebra: each coordinate satisfies exactly its prescribed `p`-th power. -/
theorem exists_frobeniusImage_presentation :
    ∃ P : Algebra.Generators k A
        (Fin (Module.finrank k (RingHom.ker (Bialgebra.counitAlgHom k A)).Cotangent)),
      (∀ i, Bialgebra.counitAlgHom k A (P.val i) = 0) ∧
      ∃ z : _ → Algebra.frobeniusImage k A p 1,
        (∀ i, (z i : A) = P.val i ^ p) ∧
        RingHom.ker (aeval (R := Algebra.frobeniusImage k A p 1) P.val) =
          Ideal.span (Set.range (fun i ↦
            (X i : MvPolynomial _ (Algebra.frobeniusImage k A p 1)) ^ p - C (z i))) := by
  classical
  let ε := Bialgebra.counitAlgHom k A
  let I := RingHom.ker ε
  let F := Algebra.frobeniusImage k A p 1
  let εF : F →ₐ[k] k := ε.comp F.val
  let : IsLocalRing F := Algebra.isLocalRing_frobeniusImage k A p 1
  let : Module.Free F A := free_frobeniusImage p
  let : Module.Finite k I.Cotangent := Module.Finite.of_surjective
    (I.toCotangent.restrictScalars k) I.toCotangent_surjective
  let b := Module.finBasis k I.Cotangent
  obtain ⟨P, hP⟩ := ε.exists_augmentation_generators_of_basis b
  choose hx hb using hP
  let x (i : Fin (Module.finrank k I.Cotangent)) : I := ⟨P.val i, hx i⟩
  obtain ⟨D, hD⟩ := Bialgebra.exists_coordinate_derivations b x hb
  let z (i : Fin (Module.finrank k I.Cotangent)) : F :=
    ⟨P.val i ^ p, ⟨P.val i, by simp only [iterateFrobenius_def, pow_one]⟩⟩
  refine ⟨P, fun i ↦ hx i, z, fun _ ↦ rfl, ?_⟩
  let J := I.frobeniusPower p
  let q : A →ₐ[k] A ⧸ J := Ideal.Quotient.mkₐ k J
  have hq (c : F) : q (algebraMap F A c) = algebraMap k (A ⧸ J) (εF c) := by
    rw [← q.commutes]
    apply Ideal.Quotient.eq.mpr
    change (c : A) - algebraMap k A (εF c) ∈ I.frobeniusPower p
    rw [ε.frobeniusPower_ker_eq_map_ker_frobeniusImage p]
    have hc : c - algebraMap k F (εF c) ∈ RingHom.ker εF := by
      simp [RingHom.mem_ker]
    exact Ideal.mem_map_of_mem F.val hc
  have hsurj : Function.Surjective (aeval (R := F) P.val) := by
    intro a
    obtain ⟨f, hf⟩ := P.aeval_val_surjective a
    refine ⟨map (algebraMap k F) f, ?_⟩
    simpa only [aeval_def, eval₂_map, IsScalarTower.algebraMap_eq k F A] using hf
  have hdiag : (Ideal.Quotient.mkₐ k J).comp (aeval (R := k) P.val) =
      aeval (R := k) (fun i ↦ q (P.val i)) := by
    ext i
    simp only [AlgHom.comp_apply, aeval_X]
    rfl
  have hker := ε.ker_frobeniusQuotient_aeval_of_coordinate p P.val
    (fun i ↦ hx i) D hD
  rw [hdiag] at hker
  exact ker_aeval_eq_span_of_nilpotent_reduction εF
    εF.isNilpotent_ker_of_finite_local q hq P.val hsurj p z
    (fun i ↦ by change ε (P.val i ^ p) = 0; rw [map_pow, hx i,
      zero_pow (Fact.out : p.Prime).ne_zero]) (fun _ ↦ rfl) hker

end HopfAlgebra
