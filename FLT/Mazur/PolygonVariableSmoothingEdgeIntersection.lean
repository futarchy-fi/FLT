/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonVariableSmoothingIntersections
public import FLT.Mazur.PolygonVariableSmoothingChartIdentification

/-!
# Full single-edge intersections of variable-smoothing charts

When two distinct cyclic nodes share only one edge, that entire Laurent edge
is their scheme-theoretic fiber product. The two-gon is excluded by the
explicit absence of the reverse edge, rather than dropping an intersection.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonVariableSmoothing
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (t : Fin n → R)
  [∀ i, Fact (IsNilpotent (t i))] (h : 2 ≤ n)
  (i k : Fin n) (hk : (finRotate n).symm i = k)
  (hne : i ≠ k) (hnr : (finRotate n).symm k ≠ i)

include hk hne hnr

/-- The full incoming puncture is exactly the inverse image of the neighboring chart. -/
theorem edge_preimage :
    chart R n t h k ⁻¹' Set.range (chart R n t h i) =
      Set.range (precedingBranch R (t k)) := by
  ext y
  constructor
  · rintro ⟨x, he⟩
    rcases (charts_eq_iff R n t h hne x y).mp he with
      ⟨z, _, _, hy⟩ | ⟨_, hz, _, _⟩
    · exact ⟨z, hy⟩
    · exact (hnr hz).elim
  · rintro ⟨z, rfl⟩
    refine ⟨leftBranchOpen R (t i) z, ?_⟩
    have he := overlap R n t h i
    rw [hk] at he
    exact congrArg (fun f ↦ f z) he

/-- The unique cyclic edge is the full intersection, including nilpotent functions. -/
theorem edge_isPullback :
    IsPullback (leftBranchOpen R (t i)) (precedingBranch R (t k))
      (chart R n t h i) (chart R n t h k) := by
  have he := overlap R n t h i
  rw [hk] at he
  apply IsOpenImmersion.isPullback _ _ _ _ he.symm
  exact TopologicalSpace.Opens.ext (edge_preimage R n t h i k hk hne hnr)

/-- Identifying both node parameters preserves the entire single-edge fiber product. -/
theorem identifiedEdge_isPullback (a b : R) (ha : a = t i) (hb : b = t k) :
    IsPullback (leftBranchOpen R a) (precedingBranch R b)
      (chartWithParameter R n t h i a ha) (chartWithParameter R n t h k b hb) := by
  subst a
  subst b
  simp only [chartWithParameter, nodeParameterIso, eqToIso_refl, Iso.refl_hom,
    Category.id_comp]
  exact edge_isPullback R n t h i k hk hne hnr

omit hk hne hnr

/-- Inverting the common edge gives the standard right terminal puncture. -/
theorem inverseEdge_isPullback {Y : Scheme} (a b : R)
    (f : PolygonSmoothing.chart R a ⟶ Y) (g : PolygonSmoothing.chart R b ⟶ Y)
    (he : IsPullback (leftBranchOpen R a) (precedingBranch R b) f g) :
    IsPullback ((edgeInversion R).hom ≫ leftBranchOpen R a) (rightBranchOpen R b) f g := by
  apply he.of_iso' (edgeInversion R) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · exact (Category.comp_id _).symm
  · change (edgeInversion R).inv ≫ (edgeInversion R).hom ≫ rightBranchOpen R b = _
    rw [Iso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The opposite retained orientation uses the other puncture of the same terminal node. -/
theorem swappedEdge_isPullback {Y : Scheme} (a b : R)
    (f : PolygonSmoothing.chart R a ⟶ Y) (g : PolygonSmoothing.chart R b ⟶ Y)
    (he : IsPullback (precedingBranch R a) (leftBranchOpen R b) f g) :
    IsPullback ((edgeInversion R).hom ≫ leftBranchOpen R a) (leftBranchOpen R b)
      ((branchSwapIso R a).hom ≫ f) g := by
  apply he.of_iso' (Iso.refl _) (branchSwapIso R a) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.id_comp, Category.assoc,
      leftBranchOpen_branchSwapIso, precedingBranch]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

end FLT.Mazur.PolygonVariableSmoothing
