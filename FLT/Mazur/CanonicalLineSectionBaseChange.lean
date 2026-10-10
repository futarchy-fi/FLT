/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CanonicalCechSectionComparison
public import FLT.Mazur.AcyclicLineSectionBaseChange

/-!
# Cover-independent base change of line sections

The equivalence constructed using a finite affine cover is the canonical
section comparison. In particular it is independent of the cover and the
proofs of cohomological flatness, and it has the expected pure-tensor formula.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules hiding map_smul
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve Chow IncreasingCechCoefficients IncreasingCechScalars

variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherian X] [X.IsSeparated]
  (f : X ⟶ S) [Flat f] (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hH : ∀ n, Module.Flat Γ(S, ⊤) (ModuleRingH f.appTop.hom L (n + 1)))
  {P T : Scheme.{0}} [IsAffine T]
  {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S} (h : IsPullback p q f g)

/-- The chosen-cover equivalence is precisely the canonical section comparison. -/
lemma sectionsEquiv_eq : (sectionsEquiv f L hL hH h).toLinearMap =
    globalComparison h L := by
  let _ := hL.isFinitePresentation
  let ι := (IdealPowerExtensionCharts.exists_finite_affine_cover (X := X)).choose
  let hι := (IdealPowerExtensionCharts.exists_finite_affine_cover (X := X)).choose_spec
  let _ : Finite ι := hι.choose
  let U := hι.choose_spec.choose
  have hU : iSup (fun i ↦ (U i).1) = ⊤ := hι.choose_spec.choose_spec
  let _ := Fintype.ofFinite ι
  let _ := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let _ (n : ℕ) := FlatLineSectionTerms.term_flat f L hL
    (fun i ↦ (U i).1) (fun i ↦ (U i).2) n
  exact cohomologicallyFlatSectionsEquiv_eq h L
    (fun i ↦ (U i).1) (fun i ↦ (U i).2) hU hH

/-- Arbitrary scalar multiples of global sections pull back by the actual adjunction unit. -/
lemma sectionsEquiv_tmul (b : Γ(T, ⊤)) (s : baseSections L f.appTop.hom ⊤) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    sectionsEquiv f L hL hH h (b ⊗ₜ[Γ(S, ⊤)] s) =
      b • (show baseSections ((pullback p).obj L) q.appTop.hom ⊤ from pullGlobal p L s) := by
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  rw [← LinearEquiv.coe_toLinearMap, sectionsEquiv_eq]
  exact globalComparison_tmul h L b s

include hL hH in
/-- The canonical section map itself is bijective under cohomological flatness. -/
theorem globalComparison_bijective : Function.Bijective (globalComparison h L) := by
  rw [← sectionsEquiv_eq f L hL hH h]
  exact (sectionsEquiv f L hL hH h).bijective

/-- Any explicit finite affine cover produces the same actual line-section comparison. -/
lemma sectionsEquiv_eq_of_cover {ι : Type} [LinearOrder ι] [Finite ι]
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤) :
    let _ := hL.isFinitePresentation
    let _ (n : ℕ) := FlatLineSectionTerms.term_flat f L hL U hU n
    sectionsEquiv f L hL hH h = cohomologicallyFlatSectionsEquiv h L U hU hCover hH := by
  dsimp only
  let _ := hL.isFinitePresentation
  let _ (n : ℕ) := FlatLineSectionTerms.term_flat f L hL U hU n
  apply LinearEquiv.toLinearMap_injective
  rw [sectionsEquiv_eq, cohomologicallyFlatSectionsEquiv_eq]

variable (hV : ∀ n, Subsingleton (ModuleH L (n + 1)))

/-- Acyclic section base change also uses the canonical map. -/
lemma acyclicSectionsEquiv_eq : (acyclicSectionsEquiv f L hL hV h).toLinearMap =
    globalComparison h L :=
  sectionsEquiv_eq f L hL (positive_flat_of_vanishing f L hV) h

/-- The acyclic comparison sends pure tensors to scalar multiples of actual section pullback. -/
lemma acyclicSectionsEquiv_tmul (b : Γ(T, ⊤)) (s : baseSections L f.appTop.hom ⊤) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    acyclicSectionsEquiv f L hL hV h (b ⊗ₜ[Γ(S, ⊤)] s) =
      b • (show baseSections ((pullback p).obj L) q.appTop.hom ⊤ from pullGlobal p L s) :=
  sectionsEquiv_tmul f L hL (positive_flat_of_vanishing f L hV) h b s

end FLT.Mazur.LineSectionBaseChange
