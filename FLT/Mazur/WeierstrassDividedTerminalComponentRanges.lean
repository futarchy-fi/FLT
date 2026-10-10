/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonNormalizationAlgebra
public import FLT.Mazur.ProjectiveLineMapRange
public import FLT.Mazur.WeierstrassDividedTerminalComponents
public import FLT.Mazur.WeierstrassDividedTerminalZeroComponents

/-!
# Complete images of the original split-terminal projective components

Each projective component contains exactly its full conic parameter and its
opposite terminal branch. Both scale-one and positive-scale constructions are covered.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open scoped Polynomial

/-- Every point of the split node belongs to one of its complete affine branches. -/
theorem terminalNodeBranches_cover {K : Type u} [Field K]
    (y : PolygonNodeBranches.node K) :
    (∃ x, PolygonCyclicAtlas.firstBranch K x = y) ∨
      ∃ x, PolygonCyclicAtlas.secondBranch K x = y := by
  obtain ⟨p, hp⟩ := PolygonNormalizationAlgebra.node_comap_surjective y
  obtain ⟨p | p, rfl⟩ := (PrimeSpectrum.primeSpectrumProd K[X] K[X]).symm.surjective p
  · rw [PrimeSpectrum.primeSpectrumProd_symm_inl, ← PrimeSpectrum.comap_comp_apply] at hp
    exact Or.inl ⟨p, hp⟩
  · rw [PrimeSpectrum.primeSpectrumProd_symm_inr, ← PrimeSpectrum.comap_comp_apply] at hp
    exact Or.inr ⟨p, hp⟩

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth) (hp : 2 * (start + j + 1) < depth)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 d)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) hp (Data.b6 d) (Data.factor6 d))

/-- The first positive-scale component contains its whole parameter and opposite terminal branch. -/
theorem terminalFirstComponent_range (hk0 : 0 < start + j) :
    Set.range (terminalFirstComponent hπ data D j hj hk0 hk hp) =
      Set.range (terminalConicFirstParameter hπ data D j hj hk0 hk) ∪
        Set.range (terminalConicSecondBranch hπ data D j hj hk hp) := by
  rw [ProjectiveLine.map_range, terminalFirstComponent_left, terminalFirstComponent_right]
  congr 1
  exact (conicZeroAffineIso c hc).hom.homeomorph.surjective.range_comp
    (terminalConicFirstParameter hπ data D j hj hk0 hk)

/-- The second positive-scale component retains its parameter and the other terminal branch. -/
theorem terminalSecondComponent_range (hk0 : 0 < start + j) :
    Set.range (terminalSecondComponent hπ data D j hj hk0 hk hp) =
      Set.range (terminalConicSecondParameter hπ data D j hj hk0 hk) ∪
        Set.range (terminalConicFirstBranch hπ data D j hj hk hp) := by
  rw [ProjectiveLine.map_range, terminalSecondComponent_left, terminalSecondComponent_right]
  congr 1
  exact (conicZeroAffineIso c hc).hom.homeomorph.surjective.range_comp
    (terminalConicSecondParameter hπ data D j hj hk0 hk)

/-- At scale one the first component likewise retains both entire affine pieces. -/
theorem terminalZeroFirstComponent_range (hk0 : start + j = 0) :
    Set.range (terminalZeroFirstComponent hπ data D j hj hk0 hk hp) =
      Set.range (terminalZeroConicFirstParameter hπ data D j hj hk0 hk) ∪
        Set.range (terminalConicSecondBranch hπ data D j hj hk hp) := by
  rw [ProjectiveLine.map_range, terminalZeroFirstComponent_left, terminalZeroFirstComponent_right]
  congr 1
  exact (conicZeroAffineIso c hc).hom.homeomorph.surjective.range_comp
    (terminalZeroConicFirstParameter hπ data D j hj hk0 hk)

/-- At scale one the second component retains its full original pieces as well. -/
theorem terminalZeroSecondComponent_range (hk0 : start + j = 0) :
    Set.range (terminalZeroSecondComponent hπ data D j hj hk0 hk hp) =
      Set.range (terminalZeroConicSecondParameter hπ data D j hj hk0 hk) ∪
        Set.range (terminalConicFirstBranch hπ data D j hj hk hp) := by
  rw [ProjectiveLine.map_range, terminalZeroSecondComponent_left, terminalZeroSecondComponent_right]
  congr 1
  exact (conicZeroAffineIso c hc).hom.homeomorph.surjective.range_comp
    (terminalZeroConicSecondParameter hπ data D j hj hk0 hk)

/-- The complete terminal branches cover exactly the original terminal chart. -/
theorem terminalConicBranches_range :
    Set.range (terminalConicFirstBranch hπ data D j hj hk hp) ∪
        Set.range (terminalConicSecondBranch hπ data D j hj hk hp) =
      Set.range (terminalNodeChart hπ data D (j + 1) hj (by omega) hk hp) := by
  ext z
  constructor
  · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · exact ⟨PolygonCyclicAtlas.firstBranch (ResidueField R) x, rfl⟩
    · exact ⟨PolygonCyclicAtlas.secondBranch (ResidueField R) x, rfl⟩
  · rintro ⟨x, rfl⟩
    rcases terminalNodeBranches_cover x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl ⟨y, rfl⟩
    · exact Or.inr ⟨y, rfl⟩

/-- The terminal pair includes the whole terminal chart and both complete conic parameters. -/
theorem terminalComponents_range (hk0 : 0 < start + j) :
    Set.range (terminalFirstComponent hπ data D j hj hk0 hk hp) ∪
        Set.range (terminalSecondComponent hπ data D j hj hk0 hk hp) =
      (Set.range (terminalConicFirstParameter hπ data D j hj hk0 hk) ∪
        Set.range (terminalConicSecondParameter hπ data D j hj hk0 hk)) ∪
      Set.range (terminalNodeChart hπ data D (j + 1) hj (by omega) hk hp) := by
  rw [terminalFirstComponent_range, terminalSecondComponent_range,
    ← terminalConicBranches_range hπ data D j hj hk hp]
  ext x
  simp only [Set.mem_union]
  tauto

/-- The scale-one pair has the same complete coverage, with its original conic parameters. -/
theorem terminalZeroComponents_range (hk0 : start + j = 0) :
    Set.range (terminalZeroFirstComponent hπ data D j hj hk0 hk hp) ∪
        Set.range (terminalZeroSecondComponent hπ data D j hj hk0 hk hp) =
      (Set.range (terminalZeroConicFirstParameter hπ data D j hj hk0 hk) ∪
        Set.range (terminalZeroConicSecondParameter hπ data D j hj hk0 hk)) ∪
      Set.range (terminalNodeChart hπ data D (j + 1) hj (by omega) hk hp) := by
  rw [terminalZeroFirstComponent_range, terminalZeroSecondComponent_range,
    ← terminalConicBranches_range hπ data D j hj hk hp]
  ext x
  simp only [Set.mem_union]
  tauto

end FLT.Mazur.WeierstrassDividedDepth
