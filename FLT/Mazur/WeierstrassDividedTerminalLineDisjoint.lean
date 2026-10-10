/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalResidueCharts
public import FLT.Mazur.WeierstrassDividedResidueMiddleIntersection
public import FLT.Mazur.WeierstrassSuccessiveXResidueBoundaryDisjoint

/-!
# Terminal charts do not meet either ordered horizontal line

The complete divided chart has empty intersection with every original
horizontal tangent line. Both terminal normalizations retain this scheme
intersection, so they cannot introduce an extra incidence or identify the lines.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
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
local notation "f" => globalDividedTensorChart hπ data K (j + 1) hj
variable (s : ResidueField R) (hs : s * (s + residue R W.a₁) = 0)
local notation "L" => residueSuccessiveLineImmersion D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) s hs

/-- The full divided chart misses any original horizontal tangent line scheme-theoretically. -/
theorem globalDividedLine_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) f (L ≫ g) := by
  have H := residueLineBoundary_isPullback D (start + j) hk0 hk
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) s hs
  convert! H.paste_horiz
    (globalResidue_middleOverlap_isPullback hπ data D j hj hk0 hk) using 1
  exact Scheme.empty_ext _ _

/-- There is no point common to a horizontal tangent line and the complete divided chart. -/
theorem globalDividedLine_disjoint : Disjoint (Set.range f) (Set.range (L ≫ g)) := by
  apply Scheme.isEmpty_pullback_iff.mp
  let E := (globalDividedLine_isPullback hπ data D j hj hk0 hk s hs).isoPullback
  exact E.symm.hom.homeomorph.isEmpty

section Laurent
variable (hp : 2 * (start + j + 1) = depth)
local notation "G" => terminalLaurentChart hπ data D (j + 1) hj hk' hk hp

/-- The full laurent terminal normalization remains disjoint from each horizontal line. -/
theorem terminalLaurentLine_disjoint : Disjoint (Set.range G) (Set.range (L ≫ g)) := by
  rw [terminalLaurentChart_range]
  exact globalDividedLine_disjoint hπ data D j hj hk0 hk s hs

/-- The entire laurent terminal-line fiber product is the empty scheme. -/
theorem terminalLaurentLine_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) G (L ≫ g) := by
  let _ := Scheme.isEmpty_pullback G (L ≫ g)
    (terminalLaurentLine_disjoint hπ data D j hj hk0 hk s hs hp)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback G (L ≫ g))))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

end Laurent

section Node
variable (hp : 2 * (start + j + 1) < depth)
local notation "G" => terminalNodeChart hπ data D (j + 1) hj hk' hk hp

/-- The full node terminal normalization remains disjoint from each horizontal line. -/
theorem terminalNodeLine_disjoint : Disjoint (Set.range G) (Set.range (L ≫ g)) := by
  rw [terminalNodeChart_range]
  exact globalDividedLine_disjoint hπ data D j hj hk0 hk s hs

/-- The entire node terminal-line fiber product is the empty scheme. -/
theorem terminalNodeLine_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) G (L ≫ g) := by
  let _ := Scheme.isEmpty_pullback G (L ≫ g)
    (terminalNodeLine_disjoint hπ data D j hj hk0 hk s hs hp)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback G (L ≫ g))))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

end Node

end FLT.Mazur.WeierstrassDividedDepth
