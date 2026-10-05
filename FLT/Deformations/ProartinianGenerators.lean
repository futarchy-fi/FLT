/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.ProartinianNakayama
public import FLT.Deformations.ProartinianAdicTopology

/-!
# Lifting finite generators from an open quotient

An open closed relative-square ideal suffices to obtain actual finite
maximal-ideal generators and adic completeness. The openness hypothesis is
explicit: identifying a continuous dual alone does not supply it.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace Deformation.ProartinianCat

variable {O : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
  (A : ProartinianCat O)

/-- Lift the finitely many maximal-ideal classes of a finite open quotient. -/
theorem exists_fg_maximalIdeal_mod_open (I : OpenIdeal A) :
    ∃ J : Ideal A, J.FG ∧ J ≤ maximalIdeal A ∧
      maximalIdeal A ≤ J ⊔ OpenIdeal.ideal I := by
  let f := Ideal.Quotient.mk (OpenIdeal.ideal I)
  let S : Set (A ⧸ OpenIdeal.ideal I) := f '' (maximalIdeal A : Set A)
  have hx : ∀ q : S, ∃ a : A, a ∈ maximalIdeal A ∧ f a = q.1 := by
    intro q
    exact q.2
  choose x hx hxq using hx
  let J : Ideal A := Ideal.span (Set.range x)
  have hJ : J ≤ maximalIdeal A := Ideal.span_le.mpr (by rintro _ ⟨q, rfl⟩; exact hx q)
  refine ⟨J, Submodule.fg_span (Set.finite_range x), hJ, ?_⟩
  intro a ha
  let q : S := ⟨f a, ⟨a, ha, rfl⟩⟩
  have hi : a - x q ∈ OpenIdeal.ideal I := Ideal.Quotient.eq.mp (hxq q).symm
  exact Submodule.mem_sup.mpr ⟨x q, Ideal.subset_span ⟨q, rfl⟩,
    a - x q, hi, by abel⟩

/-- A proper open ideal contained in the closed relative-square sum produces
finite generators of the actual maximal ideal. -/
theorem maximalIdeal_fg_of_open_le_closure (C : Ideal A) (hC : C.FG)
    (hCm : C ≤ maximalIdeal A) (I : OpenIdeal A)
    (hI : OpenIdeal.ideal I ≤ (C ⊔ maximalIdeal A ^ 2).closure) :
    (maximalIdeal A).FG := by
  obtain ⟨J, hJ, hJm, hm⟩ := exists_fg_maximalIdeal_mod_open A I
  have heq : maximalIdeal A = J ⊔ C :=
    maximalIdeal_eq_of_fg_of_le_closure_sup_square A (J ⊔ C) (Submodule.FG.sup hJ hC)
      (sup_le hJm hCm) (by
        intro a ha
        obtain ⟨j, hj, i, hi, rfl⟩ := Submodule.mem_sup.mp (hm ha)
        apply Ideal.add_mem
        · exact subset_closure ((le_sup_left.trans le_sup_left :
            J ≤ J ⊔ C ⊔ maximalIdeal A ^ 2) hj)
        · exact closure_mono (show C ⊔ maximalIdeal A ^ 2 ≤
            J ⊔ C ⊔ maximalIdeal A ^ 2 from sup_le_sup_right le_sup_right _) (hI hi))
  rw [heq]
  exact Submodule.FG.sup hJ hC

/-- Under the same explicit openness condition, the original topology is adic. -/
theorem isAdicTopology_of_open_le_closure (C : Ideal A) (hC : C.FG)
    (hCm : C ≤ maximalIdeal A) (I : OpenIdeal A)
    (hI : OpenIdeal.ideal I ≤ (C ⊔ maximalIdeal A ^ 2).closure) : IsAdicTopology A :=
  isAdicTopology_of_maximalIdeal_fg A (maximalIdeal_fg_of_open_le_closure A C hC hCm I hI)

/-- The same condition gives completeness for the actual maximal-ideal filtration. -/
theorem isAdicComplete_of_open_le_closure (C : Ideal A) (hC : C.FG)
    (hCm : C ≤ maximalIdeal A) (I : OpenIdeal A)
    (hI : OpenIdeal.ideal I ≤ (C ⊔ maximalIdeal A ^ 2).closure) :
    IsAdicComplete (maximalIdeal A) A :=
  isAdicComplete_of_maximalIdeal_fg A (maximalIdeal_fg_of_open_le_closure A C hC hCm I hI)

end Deformation.ProartinianCat
