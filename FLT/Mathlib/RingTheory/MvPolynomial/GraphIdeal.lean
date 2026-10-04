/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.TranslatedVariables
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Graph equations for adjoining redundant polynomial coordinates -/

@[expose] public noncomputable section

namespace MvPolynomial

variable {R A σ : Type*} [CommRing R] [CommRing A]

/-- A polynomial differs from its value by an element of the graph ideal. -/
theorem sub_C_eval_mem_graph (a : σ → R) (p : MvPolynomial σ R) :
    p - C (eval a p) ∈ Ideal.span (Set.range fun i ↦ X i - C (a i)) := by
  let J : Ideal (MvPolynomial σ R) := Ideal.span (Set.range fun i ↦ X i - C (a i))
  let q := Ideal.Quotient.mk J
  have hx (i : σ) : q (X i) = q (C (a i)) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  have he : q = (q.comp C).comp (eval a) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simpa using hx i
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, sub_eq_zero]
  exact DFunLike.congr_fun he p

/-- Pulling back any coefficient ideal by evaluation adds exactly the graph equations. -/
theorem comap_eval_eq_graph_sup (a : σ → R) (I : Ideal R) :
    I.comap (eval a) =
      Ideal.span (Set.range fun i ↦ X i - C (a i)) ⊔ I.map C := by
  apply le_antisymm
  · intro p hp
    have hd := (show Ideal.span (Set.range fun i ↦ X i - C (a i)) ≤
      Ideal.span (Set.range fun i ↦ X i - C (a i)) ⊔ I.map C from le_sup_left)
        (sub_C_eval_mem_graph a p)
    have hc := (show I.map C ≤
      Ideal.span (Set.range fun i ↦ X i - C (a i)) ⊔ I.map C from le_sup_right)
        (Ideal.mem_map_of_mem C hp)
    simpa only [sub_add_cancel] using Ideal.add_mem _ hd hc
  · apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change eval a (X i - C (a i)) ∈ I
      simp
    · apply Ideal.map_le_iff_le_comap.mpr
      intro r hr
      change eval a (C r) ∈ I
      simpa using hr

/-- The graph equations generate the complete evaluation kernel. -/
theorem ker_eval_eq_graph (a : σ → R) :
    RingHom.ker (eval a) = Ideal.span (Set.range fun i ↦ X i - C (a i)) := by
  simpa only [RingHom.ker, Ideal.map_bot, sup_bot_eq] using comap_eval_eq_graph_sup a ⊥

/-- Adding redundant coordinates adds graph equations to the original relation ideal. -/
theorem ker_comp_eval_eq_graph_sup (f : R →+* A) (a : σ → R) :
    RingHom.ker (f.comp (eval a)) =
      Ideal.span (Set.range fun i ↦ X i - C (a i)) ⊔ (RingHom.ker f).map C := by
  rw [← RingHom.comap_ker, comap_eval_eq_graph_sup]

/-- For finitely many added variables the complete kernel is an explicit ordered list. -/
theorem ker_comp_eval_eq_ofList {n : ℕ} (f : R →+* A) (a : Fin n → R)
    (rs : List R) (hker : RingHom.ker f = Ideal.ofList rs) :
    RingHom.ker (f.comp (eval a)) =
      Ideal.ofList (((List.finRange n).map fun i ↦ X i - C (a i)) ++ rs.map C) := by
  rw [ker_comp_eval_eq_graph_sup, hker, Ideal.ofList_append, Ideal.map_ofList]
  congr 1
  congr 1
  ext p
  simp

end MvPolynomial
