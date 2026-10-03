/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Quotient.Card

/-!
# Cardinal arithmetic for finite periodic homology

Counting kernels and images proves equality of the two homology orders
of a two-periodic complex on a finite module.
-/

@[expose] public noncomputable section

universe u v

namespace LocalClassFieldTheory

open CategoryTheory

variable {R : Type u} {M N : Type v} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The first isomorphism theorem gives the kernel-image cardinal identity. -/
theorem linearMap_card_eq_ker_mul_range (f : M →ₗ[R] N) :
    Nat.card M = Nat.card f.ker * Nat.card f.range := by
  rw [f.ker.card_eq_card_quotient_mul_card]
  congr 1
  exact Nat.card_congr f.quotKerEquivRange.toEquiv

/-- Restricting the codomain to cycles does not change the size of the image. -/
theorem shortComplex_card_toCycles_range (S : ShortComplex (ModuleCat.{v} R)) :
    Nat.card S.moduleCatToCycles.range = Nat.card S.f.hom.range := by
  apply Nat.card_congr
  refine Equiv.ofBijective (fun x => ⟨x.val.val, ?_⟩) ?_
  · obtain ⟨y, hy⟩ := x.property
    exact ⟨y, congrArg Subtype.val hy⟩
  · constructor
    · intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun w : S.f.hom.range => w.val) h
    · rintro ⟨x, y, rfl⟩
      exact ⟨⟨S.moduleCatToCycles y, ⟨y, rfl⟩⟩, rfl⟩

/-- Cycles are counted by image order times actual homology order. -/
theorem shortComplex_card_cycles (S : ShortComplex (ModuleCat.{v} R)) :
    Nat.card S.g.hom.ker = Nat.card S.f.hom.range * Nat.card S.homology := by
  rw [S.moduleCatToCycles.range.card_eq_card_quotient_mul_card,
    shortComplex_card_toCycles_range]
  congr 1
  exact Nat.card_congr S.moduleCatHomologyIso.toLinearEquiv.toEquiv.symm

/-- A short complex with finite middle module has finite homology. -/
theorem shortComplex_homology_finite (S : ShortComplex (ModuleCat.{v} R)) [Finite S.X₂] :
    Finite S.homology := by
  let : Finite (S.g.hom.ker ⧸ S.moduleCatToCycles.range) :=
    Finite.of_surjective _ S.moduleCatToCycles.range.mkQ_surjective
  exact Finite.of_equiv (S.g.hom.ker ⧸ S.moduleCatToCycles.range)
    S.moduleCatHomologyIso.toLinearEquiv.toEquiv.symm

/-- The two homology groups of a finite two-periodic module have equal cardinality. -/
theorem finite_periodic_homology_card [Finite M] (f g : M →ₗ[R] M)
    (hfg : g.comp f = 0) (hgf : f.comp g = 0) :
    Nat.card (ShortComplex.moduleCatMk f g hfg).homology =
      Nat.card (ShortComplex.moduleCatMk g f hgf).homology := by
  have hf := linearMap_card_eq_ker_mul_range f
  have hg := linearMap_card_eq_ker_mul_range g
  have hfg' := shortComplex_card_cycles (ShortComplex.moduleCatMk f g hfg)
  have hgf' := shortComplex_card_cycles (ShortComplex.moduleCatMk g f hgf)
  change Nat.card g.ker = Nat.card f.range * _ at hfg'
  change Nat.card f.ker = Nat.card g.range * _ at hgf'
  have he : (Nat.card f.range * Nat.card g.range) *
      Nat.card (ShortComplex.moduleCatMk f g hfg).homology =
      (Nat.card f.range * Nat.card g.range) *
        Nat.card (ShortComplex.moduleCatMk g f hgf).homology := by
    calc
      _ = Nat.card g.ker * Nat.card g.range := by rw [hfg']; ring
      _ = Nat.card f.ker * Nat.card f.range := hg.symm.trans hf
      _ = _ := by rw [hgf']; ring
  have hp : 0 < Nat.card f.range * Nat.card g.range :=
    Nat.mul_pos (Nat.card_pos) (Nat.card_pos)
  exact Nat.eq_of_mul_eq_mul_left hp he

end LocalClassFieldTheory
