/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCharpolyCharts

/-!
# Gluing coefficients over the whole original target

Independent local finite bases give compatible coefficients on intersections.
The original structure sheaf glues each coefficient, and any other finite free
chart computes its restriction. No common rank or invariant chart is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineCharpolyCoefficientGluing
open AffineCharpolyCharts
universe u v w
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [IsAffine Y]

/-- Arbitrary finite free charts have the same coefficients on their overlap. -/
theorem chart_overlap (U V : Y.affineOpens)
    (hU : AffineOpenNorm.HasBasis f U) (hV : AffineOpenNorm.HasBasis f V)
    (s : Γ(X, ⊤)) (n : ℕ) :
    Y.presheaf.map (homOfLE inf_le_left).op (chart f U hU s n) =
      Y.presheaf.map (homOfLE inf_le_right).op (chart f V hV s n) := by
  let W : Y.affineOpens := ⟨U.1 ⊓ V.1, U.2.inf V.2⟩
  have h₁ : W ≤ U := show U.1 ⊓ V.1 ≤ U.1 from inf_le_left
  have h₂ : W ≤ V := show U.1 ⊓ V.1 ≤ V.1 from inf_le_right
  have hW := hU.restrict f h₁
  exact (chart_restrict f hU hW h₁ s n).trans
    (chart_restrict f hV hW h₂ s n).symm

variable {ι : Type v} (U : ι → Y.affineOpens)
  (hU : ∀ i, AffineOpenNorm.HasBasis f (U i)) (hcover : ⨆ i, (U i).1 = ⊤)

include hcover in
/-- Each local multiplication coefficient glues uniquely in the original sheaf. -/
theorem existsUnique_coefficient (s : Γ(X, ⊤)) (n : ℕ) :
    ∃! t : Γ(Y, ⊤), ∀ i,
      Y.presheaf.map (homOfLE le_top).op t = chart f (U i) (hU i) s n := by
  exact Y.sheaf.existsUnique_gluing' (fun i ↦ (U i).1) ⊤
    (fun _ ↦ homOfLE le_top) (ge_of_eq hcover) (fun i ↦ chart f (U i) (hU i) s n)
    (fun i j ↦ chart_overlap f (U i) (U j) (hU i) (hU j) s n)

/-- The global coefficient supplied by the structure sheaf, with no chosen global basis. -/
def coefficient (s : Γ(X, ⊤)) (n : ℕ) : Γ(Y, ⊤) :=
  (existsUnique_coefficient f U hU hcover s n).choose

/-- Every chosen chart recovers its actual characteristic coefficient. -/
theorem coefficient_chart (s : Γ(X, ⊤)) (n : ℕ) (i : ι) :
    Y.presheaf.map (homOfLE le_top).op (coefficient f U hU hcover s n) =
      chart f (U i) (hU i) s n :=
  (existsUnique_coefficient f U hU hcover s n).choose_spec.1 i

/-- Equality with a coefficient is detected on the entire chosen cover. -/
theorem eq_coefficient (s : Γ(X, ⊤)) (n : ℕ) (t : Γ(Y, ⊤))
    (ht : ∀ i, Y.presheaf.map (homOfLE le_top).op t = chart f (U i) (hU i) s n) :
    t = coefficient f U hU hcover s n :=
  (existsUnique_coefficient f U hU hcover s n).choose_spec.2 t ht

/-- Any additional finite free chart computes the same global coefficient. -/
theorem coefficient_any_chart (V : Y.affineOpens) (hV : AffineOpenNorm.HasBasis f V)
    (s : Γ(X, ⊤)) (n : ℕ) :
    Y.presheaf.map (homOfLE le_top).op (coefficient f U hU hcover s n) =
      chart f V hV s n := by
  apply Y.sheaf.eq_of_locally_eq' (fun i ↦ V.1 ⊓ (U i).1) V.1
    (fun _ ↦ homOfLE inf_le_left) (by rw [← inf_iSup_eq, hcover, inf_top_eq])
  intro i
  let W : Y.affineOpens := ⟨V.1 ⊓ (U i).1, V.2.inf (U i).2⟩
  have hWV : W ≤ V := show V.1 ⊓ (U i).1 ≤ V.1 from inf_le_left
  have hWU : W ≤ U i := show V.1 ⊓ (U i).1 ≤ (U i).1 from inf_le_right
  have hW := hV.restrict f hWV
  change Y.presheaf.map (homOfLE hWV).op
    (Y.presheaf.map (homOfLE le_top).op (coefficient f U hU hcover s n)) =
      Y.presheaf.map (homOfLE hWV).op (chart f V hV s n)
  rw [chart_restrict f hV hW hWV]
  have hi := congrArg (Y.presheaf.map (homOfLE hWU).op)
    (coefficient_chart f U hU hcover s n i)
  rw [chart_restrict f (hU i) hW hWU] at hi
  simp only [← CommRingCat.comp_apply, ← Functor.map_comp] at hi ⊢
  convert hi using 2

/-- All coefficients are independent of the entire finite free cover and its bases. -/
theorem coefficient_independent {κ : Type w} (V : κ → Y.affineOpens)
    (hV : ∀ j, AffineOpenNorm.HasBasis f (V j)) (hcoverV : ⨆ j, (V j).1 = ⊤)
    (s : Γ(X, ⊤)) (n : ℕ) :
    coefficient f U hU hcover s n = coefficient f V hV hcoverV s n := by
  apply eq_coefficient
  intro j
  exact coefficient_any_chart f U hU hcover (V j) (hV j) s n

end FLT.Mazur.AffineCharpolyCoefficientGluing
