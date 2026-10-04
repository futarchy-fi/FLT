/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Ideal.QuotientUnitCertificate
public import FLT.Mathlib.RingTheory.MvPolynomial.EnlargedCoefficientStage

/-! # Descend a finite principal-cover certificate to an enlarged coefficient stage -/

@[expose] public noncomputable section

namespace MvPolynomial

variable {R σ ι κ : Type*} [CommRing R] [Finite ι] [Finite κ]

/-- Relations and principal opens forming a cover descend to a common enlarged Noetherian
stage where they still form a cover. All relation-ideal witnesses are included in the stage. -/
theorem exists_unitIdeal_certificate_stage (S : Subalgebra ℤ R) (hS : S.FG)
    (f : ι → MvPolynomial σ R) (g : κ → MvPolynomial σ R)
    (h : Ideal.span (Set.range fun j ↦
      Ideal.Quotient.mk (Ideal.span (Set.range f)) (g j)) = ⊤) :
    ∃ T : Subalgebra ℤ R, S ≤ T ∧ T.FG ∧ IsNoetherianRing T ∧
      ∃ (f' : ι → MvPolynomial σ T) (g' : κ → MvPolynomial σ T),
        (∀ i, map T.val.toRingHom (f' i) = f i) ∧
        (∀ j, map T.val.toRingHom (g' j) = g j) ∧
        Ideal.span (Set.range fun j ↦
          Ideal.Quotient.mk (Ideal.span (Set.range f')) (g' j)) = ⊤ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype κ := Fintype.ofFinite κ
  obtain ⟨a, b, hab⟩ := Ideal.exists_unit_certificate_of_quotient_span_eq_top f g h
  let data : (ι ⊕ κ) ⊕ (ι ⊕ κ) → MvPolynomial σ R :=
    Sum.elim (Sum.elim f g) (Sum.elim b a)
  obtain ⟨T, hST, hT, hN, d, hd⟩ := exists_coefficient_stage_above S hS data
  let f' := fun i ↦ d (.inl (.inl i))
  let g' := fun j ↦ d (.inl (.inr j))
  let b' := fun i ↦ d (.inr (.inl i))
  let a' := fun j ↦ d (.inr (.inr j))
  have hf (i) : map T.val.toRingHom (f' i) = f i := hd (.inl (.inl i))
  have hg (j) : map T.val.toRingHom (g' j) = g j := hd (.inl (.inr j))
  have hb (i) : map T.val.toRingHom (b' i) = b i := hd (.inr (.inl i))
  have ha (j) : map T.val.toRingHom (a' j) = a j := hd (.inr (.inr j))
  have hab' : ∑ j, a' j * g' j + ∑ i, b' i * f' i = 1 := by
    apply map_injective T.val.toRingHom Subtype.val_injective
    simpa only [map_add, map_sum, map_mul, hf, hg, hb, ha, map_one] using hab
  let I := Ideal.span (Set.range f')
  have hq (i) : Ideal.Quotient.mk I (f' i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  have heq : ∑ j, Ideal.Quotient.mk I (a' j) * Ideal.Quotient.mk I (g' j) = 1 := by
    simpa only [map_add, map_sum, map_mul, map_one, hq, mul_zero,
      Finset.sum_const_zero, add_zero] using congrArg (Ideal.Quotient.mk I) hab'
  refine ⟨T, hST, hT, hN, f', g', hf, hg, (Ideal.eq_top_iff_one _).mpr ?_⟩
  exact Ideal.mem_span_range_iff_exists_fun.mpr ⟨fun j ↦ Ideal.Quotient.mk I (a' j), heq⟩

/-- For data already chosen at a coefficient stage, the enlarged certificate uses their
canonical images under the inclusion, rather than a newly chosen presentation. -/
theorem exists_unitIdeal_certificate_stage_of_stage (S : Subalgebra ℤ R) (hS : S.FG)
    (f : ι → MvPolynomial σ S) (g : κ → MvPolynomial σ S)
    (h : Ideal.span (Set.range fun j ↦ Ideal.Quotient.mk
      (Ideal.span (Set.range fun i ↦ map S.val.toRingHom (f i)))
      (map S.val.toRingHom (g j))) = ⊤) :
    ∃ (T : Subalgebra ℤ R) (hST : S ≤ T), T.FG ∧ IsNoetherianRing T ∧
      Ideal.span (Set.range fun j ↦ Ideal.Quotient.mk
        (Ideal.span (Set.range fun i ↦ map (Subalgebra.inclusion hST).toRingHom (f i)))
        (map (Subalgebra.inclusion hST).toRingHom (g j))) = ⊤ := by
  obtain ⟨T, hST, hT, hN, f', g', hf, hg, hspan⟩ :=
    exists_unitIdeal_certificate_stage S hS
      (fun i ↦ map S.val.toRingHom (f i)) (fun j ↦ map S.val.toRingHom (g j)) h
  have he {x : MvPolynomial σ S} {y : MvPolynomial σ T}
      (hy : map T.val.toRingHom y = map S.val.toRingHom x) :
      y = map (Subalgebra.inclusion hST).toRingHom x := by
    apply map_injective T.val.toRingHom Subtype.val_injective
    rw [map_map, hy]
    rfl
  have hf' : f' = fun i ↦ map (Subalgebra.inclusion hST).toRingHom (f i) :=
    funext fun i ↦ he (hf i)
  have hg' : g' = fun j ↦ map (Subalgebra.inclusion hST).toRingHom (g j) :=
    funext fun j ↦ he (hg j)
  subst f' g'
  exact ⟨T, hST, hT, hN, hspan⟩

end MvPolynomial
