/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalConicBranches
public import FLT.Mazur.PolygonNodeDifferenceOpen

/-!
# Completeness of the two original punctured conic parameters

The ordered Laurent punctures cover the entire conic incidence open and are
disjoint. Their normalized images are precisely the two terminal node
branches, with no additional point lost from the boundary.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Precomposing a scheme map with an isomorphism retains its whole image. -/
theorem conicBoundary_range_iso_comp {X Y Z : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ Z) :
    Set.range (e.hom ≫ f) = Set.range f :=
  e.hom.homeomorph.surjective.range_comp f

/-- The spectrum map of the full principal localization has the expected image. -/
theorem conicBoundary_range_away {A : Type u} [CommRing A] (x : A) :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x)))) =
      (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum A)) :=
  PrimeSpectrum.localization_away_comap_range (Localization.Away x) x

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "tx" => WeierstrassDilatation.tensorX W (π ^ (start + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) K
local notation "t" => WeierstrassSuccessiveX.coord W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) 0
local notation "m" => WeierstrassSuccessiveX.residueMiddleTransition D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
local notation "hk'" => Nat.zero_lt_succ (start + j)

open WeierstrassSuccessiveX WeierstrassModificationX
local notation "W₀" => W.map (residue R)
local notation "c" => residue R (Data.b6 d)
local notation "B" => MiddleConicOpen W₀ c
local notation "C₀" => ConicCoordinate (WeierstrassCurve.a₁ W₀) c
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap C₀ B))
local notation "C" => residueSuccessiveConicImmersion D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
local notation "g" => globalSuccessiveTensorChart hπ data K j hj
local notation "E" => residueConicBoundaryIso D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)

local notation "φ" => residueDividedConicMap D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
local notation "f" => globalDividedTensorChart hπ data K (j + 1) hj

variable (hp : 2 * (start + j + 1) < depth)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) hp (Data.b6 d) (Data.factor6 d))
local notation "ha" => D.a₁_unit.map (residue R)
local notation "f₁" => conicBoundaryFirst W₀ c ha hc
local notation "f₂" => conicBoundarySecond W₀ c ha hc
local notation "ψ" => residueNodeConicMap D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "G" => terminalNodeChart hπ data D (j + 1) hj hk' hk hp
local notation "ι" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (AlgEquiv.toAlgHom (LaurentPolynomial.invert (R := K)))))
local notation "p₀" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicZeroPuncture c hc)))

local notation "s" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "s₁" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f₁))
local notation "s₂" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f₂))
local notation "e" => WeierstrassDilatation.residuePolygonEquiv D (start + (j + 1)) hk' hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away ((e) tx))))
local notation "a" => WeierstrassDilatation.residueTangentUnit D
local notation "I" => Scheme.Spec.mapIso (Iso.op (RingEquiv.toCommRingCatIso
  (AlgEquiv.toRingEquiv (LaurentPolynomial.invert (R := K)))))

include hπ hk0 hk in
/-- The full terminal-conic boundary consists of exactly the two punctured node branches. -/
theorem terminalNodeConicCoordinates_range :
    Set.range s = Set.range (PolygonNodeBranches.left K) ∪
      Set.range (PolygonNodeBranches.right K) := by
  rw [terminalNodeConicCoordinates_eq_boundary hπ data D j hj hk0 hk hp]
  rw [conicBoundary_range_iso_comp]
  have hx : (e) tx = algebraMap K _ (↑(a)⁻¹ : K) *
      (PolygonNodeLocalization.y - PolygonNodeLocalization.x) :=
    WeierstrassDilatation.residuePolygonEquiv_x D (start + j + 1) hk' hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d)
      (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
  exact (conicBoundary_range_away _).trans
    ((congrArg (fun z : PolygonNodeEqualizer.A (R := K) =>
      (PrimeSpectrum.basicOpen z : Set (PrimeSpectrum (PolygonNodeEqualizer.A (R := K))))) hx).trans
      (PolygonNodeBranches.branches_cover_difference (a)⁻¹).symm)

omit [IsBezout R] in
/-- The first ordered puncture has the whole right branch as its normalized image. -/
theorem terminalNodeConicFirst_range : Set.range (s₁ ≫ s) =
    Set.range (PolygonNodeBranches.right K) := by
  rw [residueNodeConicFirst_spec]
  change Set.range (fun z => PolygonNodeBranches.right K ((I).hom z)) = _
  exact (I).hom.homeomorph.surjective.range_comp _

omit [IsBezout R] in
/-- The second ordered puncture has the whole left branch as its normalized image. -/
theorem terminalNodeConicSecond_range : Set.range (s₂ ≫ s) =
    Set.range (PolygonNodeBranches.left K) := by
  rw [residueNodeConicSecond_spec]
  change Set.range (fun z => PolygonNodeBranches.left K ((I).hom z)) = _
  exact (I).hom.homeomorph.surjective.range_comp _

include hπ hk0 hk in
/-- The two actual conic punctures cover every point of the original incidence open. -/
theorem terminalConicPunctures_cover : Set.range s₁ ∪ Set.range s₂ = Set.univ := by
  let _ : IsOpenImmersion s := by
    rw [terminalNodeConicCoordinates_eq_boundary hπ data D j hj hk0 hk hp]
    infer_instance
  ext z
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  have hz : s z ∈ Set.range (PolygonNodeBranches.left K) ∪
      Set.range (PolygonNodeBranches.right K) := by
    rw [← terminalNodeConicCoordinates_range hπ data D j hj hk0 hk hp]
    exact ⟨z, rfl⟩
  rcases hz with hz | hz
  · rw [← terminalNodeConicSecond_range data D j hj hk hp] at hz
    obtain ⟨p, hp⟩ := hz
    exact Or.inr ⟨p, (s).isOpenEmbedding.injective hp⟩
  · rw [← terminalNodeConicFirst_range data D j hj hk hp] at hz
    obtain ⟨p, hp⟩ := hz
    exact Or.inl ⟨p, (s).isOpenEmbedding.injective hp⟩

omit [IsBezout R] in
include hk in
/-- The two original punctures share no point, before or after their terminal identification. -/
theorem terminalConicPunctures_disjoint : Disjoint (Set.range s₁) (Set.range s₂) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨p, rfl⟩ ⟨q, hq⟩
  have h₁ : s (s₁ p) ∈ Set.range (PolygonNodeBranches.right K) := by
    rw [← terminalNodeConicFirst_range data D j hj hk hp]
    exact ⟨p, rfl⟩
  have h₂ : s (s₁ p) ∈ Set.range (PolygonNodeBranches.left K) := by
    rw [← terminalNodeConicSecond_range data D j hj hk hp]
    exact ⟨q, congrArg s hq⟩
  exact Set.disjoint_left.mp (PolygonNodeBranches.disjoint_ranges K) h₂ h₁

end FLT.Mazur.WeierstrassDividedDepth
