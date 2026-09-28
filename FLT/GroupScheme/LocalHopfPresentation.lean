/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FrobeniusPresentationDescent
public import FLT.Mathlib.RingTheory.CotangentSubfamily
public import FLT.Mathlib.RingTheory.LocalFrobeniusInduction
public import FLT.Mathlib.RingTheory.MvPolynomial.RedundantCoordinates
public import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# Square presentations of finite local commutative Hopf algebras

Over a perfect field of positive characteristic, every finite augmentation
coordinate family presenting a finite local commutative Hopf algebra has
one defining relation per coordinate. In particular, choosing cotangent
coordinates gives exactly the cotangent dimension many generators and
relations. The proof descends through strictly smaller Frobenius images.
-/

@[expose] public noncomputable section

universe u v

namespace HopfAlgebra

open MvPolynomial

variable {k A : Type u} [Field k] [CommRing A] [HopfAlgebra k A]
  [IsLocalRing A] [Module.Finite k A]
  (p : ℕ) [Fact p.Prime] [CharP k p] [CharP A p] [PerfectRing k p]

include p

/-- Every finite augmentation coordinate presentation of a finite local
commutative Hopf algebra has one generating relation per coordinate. -/
theorem exists_relations_of_generators (A : Type u)
    [CommRing A] [HopfAlgebra k A] [IsLocalRing A] [Module.Finite k A] [CharP A p]
    {ι : Type v} [Finite ι]
    (x : ι → A) (hx : ∀ i, Bialgebra.counitAlgHom k A (x i) = 0)
    (hsurj : Function.Surjective (aeval (R := k) x)) :
    ∃ r : ι → MvPolynomial ι k,
      RingHom.ker (aeval (R := k) x) = Ideal.span (Set.range r) := by
  classical
  let ε := Bialgebra.counitAlgHom k A
  by_cases hA : (⊥ : Subalgebra k A) = ⊤
  · have hx0 : x = fun _ ↦ 0 := by
      funext i
      have hm : x i ∈ (⊥ : Subalgebra k A) := by rw [hA]; trivial
      obtain ⟨c, hc⟩ := Algebra.mem_bot.mp hm
      have hc0 : c = 0 := by
        have he := hx i
        rw [← hc, ε.commutes] at he
        exact he
      rw [← hc, hc0, map_zero]
    refine ⟨X, ?_⟩
    rw [hx0]
    exact ker_aeval_zero_of_augmentation ε
  · obtain ⟨κ, a, ha, b, hb, hysurj⟩ :=
      ε.exists_cotangent_basis_subfamily x hx hsurj
    let : Finite κ := Finite.of_injective a ha
    let y (j : κ) : RingHom.ker ε := ⟨x (a j), hx (a j)⟩
    have hy (j : κ) : (RingHom.ker ε).toCotangent (y j) = b j :=
      (ε.augmentationCotangent_of_mem (y j)).symm.trans (hb j)
    obtain ⟨D, hD⟩ := Bialgebra.exists_coordinate_derivations b y hy
    let F := Algebra.frobeniusImage k A p 1
    let : HopfAlgebra k F := frobeniusImageHopfAlgebra p 1
    let : IsLocalRing F := Algebra.isLocalRing_frobeniusImage k A p 1
    let : CharP F p := F.val.toRingHom.charP Subtype.val_injective p
    let z (j : κ) : F :=
      ⟨x (a j) ^ p, ⟨x (a j), by simp only [iterateFrobenius_def, pow_one]⟩⟩
    have hzε (j : κ) : Bialgebra.counitAlgHom k F (z j) = 0 := by
      change ε (x (a j) ^ p) = 0
      rw [map_pow, hx, zero_pow (Fact.out : p.Prime).ne_zero]
    have hzsurj : Function.Surjective (aeval (R := k) z) :=
      aeval_frobeniusCoordinates_surjective p (x ∘ a) hysurj z (fun _ ↦ rfl)
    obtain ⟨r, hr⟩ := exists_relations_of_generators F z hzε hzsurj
    have hdesc := ker_aeval_eq_map_expand_of_coordinate p (x ∘ a)
      (fun j ↦ hx (a j)) hysurj D hD z (fun _ ↦ rfl)
    rw [hr, Ideal.map_span, ← Set.range_comp] at hdesc
    exact exists_ker_eq_span_of_injective_coordinates x a ha hysurj
      (fun j ↦ expand p (r j)) hdesc
termination_by Module.finrank k A
decreasing_by
  exact ε.finrank_frobeniusImage_lt p hA

omit [CharP A p] in
/-- A finite local commutative Hopf algebra over a perfect field has a
minimal polynomial presentation with exactly its cotangent dimension many
relations generating the entire kernel. -/
theorem exists_minimal_square_presentation :
    ∃ P : Algebra.Generators k A
        (Fin (Module.finrank k (RingHom.ker (Bialgebra.counitAlgHom k A)).Cotangent)),
      (∀ i, Bialgebra.counitAlgHom k A (P.val i) = 0) ∧
      ∃ r : Fin (Module.finrank k
          (RingHom.ker (Bialgebra.counitAlgHom k A)).Cotangent) → P.Ring,
        RingHom.ker (aeval (R := k) P.val) = Ideal.span (Set.range r) := by
  let : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
  let ε := Bialgebra.counitAlgHom k A
  let I := RingHom.ker ε
  let : Module.Finite k I.Cotangent := Module.Finite.of_surjective
    (I.toCotangent.restrictScalars k) I.toCotangent_surjective
  obtain ⟨P, hP⟩ := ε.exists_augmentation_generators_of_basis (Module.finBasis k I.Cotangent)
  have hx (i) : ε (P.val i) = 0 := (hP i).choose
  obtain ⟨r, hr⟩ := exists_relations_of_generators p A P.val hx P.aeval_val_surjective
  exact ⟨P, hx, r, hr⟩

omit [CharP A p] in
/-- The minimal square presentation as actual `Algebra.Presentation` data. -/
theorem exists_minimal_presentation :
    ∃ P : Algebra.Presentation k A
        (Fin (Module.finrank k (RingHom.ker (Bialgebra.counitAlgHom k A)).Cotangent))
        (Fin (Module.finrank k (RingHom.ker (Bialgebra.counitAlgHom k A)).Cotangent)),
      ∀ i, Bialgebra.counitAlgHom k A (P.val i) = 0 := by
  obtain ⟨P, hx, r, hr⟩ := exists_minimal_square_presentation (k := k) (A := A) p
  refine ⟨{ P with relation := r, span_range_relation_eq_ker := ?_ }, hx⟩
  rw [P.ker_eq_ker_aeval_val]
  exact hr.symm

end HopfAlgebra
