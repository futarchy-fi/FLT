/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineLocallyFreeRelationCharpoly

/-!
# A polynomial from the locally free characteristic coefficients

Compactness of the affine target bounds the degrees on a finite subcover.
The glued coefficients therefore have finite support and define an actual
polynomial. Its restriction is the full local characteristic polynomial.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial
namespace FLT.Mazur.AffineCharpolyCoefficientGluing
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [IsAffine Y]
  {ι : Type v} (U : ι → Y.affineOpens)
  (hU : ∀ i, AffineOpenNorm.HasBasis f (U i)) (hcover : ⨆ i, (U i).1 = ⊤)

/-- Compactness bounds the support even when local ranks are not constant. -/
theorem coefficient_eventually_zero (s : Γ(X, ⊤)) :
    ∃ N : ℕ, ∀ n, N < n → coefficient f U hU hcover s n = 0 := by
  classical
  obtain ⟨J, hJ⟩ := isCompact_univ.elim_finite_subcover
    (fun i ↦ ((U i).1 : Set Y)) (fun i ↦ (U i).1.isOpen) (by
      intro y _
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
        (show y ∈ ⨆ i, (U i).1 from hcover.symm ▸ trivial)
      exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  have hJcover : ⨆ i : J, (U i).1 = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨i, hi, hy⟩ := Set.mem_iUnion₂.mp (hJ (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hy⟩
  let Q := fun i ↦ AffineChosenBasisCharpoly.charpoly (f ∣_ (U i).1) (hU i)
    ((f ⁻¹ᵁ (U i).1).ι.appTop s)
  refine ⟨J.sup (fun i ↦ (Q i).natDegree), fun n hn ↦ ?_⟩
  apply Y.sheaf.eq_of_locally_eq' (fun i : J ↦ (U i).1) ⊤
    (fun _ ↦ homOfLE le_top) (ge_of_eq hJcover)
  intro i
  change Y.presheaf.map (homOfLE (show (U i).1 ≤ ⊤ from le_top)).op
    (coefficient f U hU hcover s n) = _
  rw [coefficient_chart, map_zero]
  change (U i).1.topIso.hom ((Q i).coeff n) = 0
  rw [coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (Finset.le_sup (f := fun i ↦ (Q i).natDegree) i.2) hn), map_zero]

/-- The glued coefficients are finitely supported in the actual global section ring. -/
theorem coefficient_finite_support (s : Γ(X, ⊤)) :
    (Function.support (coefficient f U hU hcover s)).Finite := by
  obtain ⟨N, hN⟩ := coefficient_eventually_zero f U hU hcover s
  apply (Set.finite_Iic N).subset
  intro n hn
  by_contra h
  exact hn (hN n (lt_of_not_ge h))

/-- The global characteristic polynomial constructed from the actual affine sheaf. -/
def polynomial (s : Γ(X, ⊤)) : (Γ(Y, ⊤))[X] :=
  .ofFinsupp (.ofCoeff (Finsupp.ofSupportFinite (coefficient f U hU hcover s)
    (coefficient_finite_support f U hU hcover s)))

/-- Its coefficients are exactly the uniquely glued local coefficients. -/
theorem polynomial_coeff (s : Γ(X, ⊤)) (n : ℕ) :
    (polynomial f U hU hcover s).coeff n = coefficient f U hU hcover s n := rfl

/-- The polynomial on any actual finite free chart is the usual multiplication polynomial. -/
theorem polynomial_top (V : Y.affineOpens) (hV : AffineOpenNorm.HasBasis f V)
    (s : Γ(X, ⊤)) :
    (polynomial f U hU hcover s).map V.1.ι.appTop.hom =
      AffineChosenBasisCharpoly.charpoly (f ∣_ V.1) hV ((f ⁻¹ᵁ V.1).ι.appTop s) := by
  ext n
  rw [coeff_map, polynomial_coeff]
  have h := congrArg V.1.topIso.inv (coefficient_any_chart f U hU hcover V hV s n)
  rw [AffineNormGluing.topIso_inv_global, AffineCharpolyCharts.chart_top] at h
  exact h

/-- The entire polynomial is independent of the cover, including its varying local ranks. -/
theorem polynomial_independent {κ : Type*} (V : κ → Y.affineOpens)
    (hV : ∀ j, AffineOpenNorm.HasBasis f (V j)) (hcoverV : ⨆ j, (V j).1 = ⊤)
    (s : Γ(X, ⊤)) : polynomial f U hU hcover s = polynomial f V hV hcoverV s := by
  ext n
  exact coefficient_independent f U hU hcover V hV hcoverV s n

end FLT.Mazur.AffineCharpolyCoefficientGluing
