/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResolvedAtlasPairIso

/-!
# The actual relative chart products cover the entire resolved smooth product

The pair-domain isomorphisms prove exact image equalities. Package the actual
chart products as a finite open cover, so future local formulas can descend
from these explicit sources without a separate coverage assumption.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "chart" => globalSmoothAtlasMap hπ data j hj


/-- The image of a genuine chart product is precisely its entire pair domain. -/
theorem finiteResolvedAtlasPairInput_opensRange (a b : Fin (j + 3)) :
    (finiteResolvedAtlasPairInput hπ data j hj a b).opensRange =
      finiteResolvedAtlasOpen hπ data j hj a b := by
  let _ : IsIso (finiteResolvedAtlasPairToOpen hπ data j hj a b) :=
    inferInstanceAs (IsIso (finiteResolvedAtlasPairIso hπ data j hj a b).inv)
  simp only [← finiteResolvedAtlasPairToOpen_ι, Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Opens.opensRange_ι]

/-- Every resolved smooth pair is represented in an actual relative chart product. -/
theorem finiteResolvedAtlasPairInput_covers (z : finiteResolvedProduct hπ data j hj) :
    ∃ a b x, finiteResolvedAtlasPairInput hπ data j hj a b x = z := by
  obtain ⟨a, b, hz⟩ := finiteResolvedAtlasOpen_covers hπ data j hj z
  rw [← finiteResolvedAtlasPairInput_opensRange hπ data j hj a b] at hz
  exact ⟨a, b, hz⟩

/-- A finite open cover with genuine smooth integral chart products as its sources. -/
def finiteResolvedPairCover : (finiteResolvedProduct hπ data j hj).OpenCover where
  I₀ := Fin (j + 3) × Fin (j + 3)
  X ab := pullback (chart ab.1 ≫ t) (chart ab.2 ≫ t)
  f ab := finiteResolvedAtlasPairInput hπ data j hj ab.1 ab.2
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun ab => inferInstance⟩
    intro z
    obtain ⟨a, b, x, hx⟩ := finiteResolvedAtlasPairInput_covers hπ data j hj z
    exact ⟨(a, b), x, hx⟩

/-- Equality on every genuine chart product determines the whole global morphism. -/
theorem finiteResolvedPairCover_hom_ext {Z : Scheme}
    (f g : finiteResolvedProduct hπ data j hj ⟶ Z)
    (h : ∀ a b, finiteResolvedAtlasPairInput hπ data j hj a b ≫ f =
      finiteResolvedAtlasPairInput hπ data j hj a b ≫ g) : f = g := by
  apply (finiteResolvedPairCover hπ data j hj).hom_ext
  intro ab
  exact h ab.1 ab.2

end FLT.Mazur.WeierstrassDividedDepth
