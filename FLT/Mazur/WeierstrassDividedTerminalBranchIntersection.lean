/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalNodeIncidence
public import FLT.Mazur.WeierstrassSuccessiveXTerminalBranchIntersection
public import FLT.Mazur.WeierstrassSuccessiveXConicPunctureInclusion

/-!
# Complete terminal affine branches intersect the full ordered conic parameters

The first conic parameter meets the right terminal branch, and the second
meets the left terminal branch. Both scheme intersections retain reciprocal coordinates.
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
local notation "p" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicZeroPuncture c hc)))

local notation "s₁" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f₁))
local notation "s₂" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f₂))
local notation "pT" => ProjectiveLine.overlapLeft K
local notation "B₁" => terminalConicFirstBranch hπ data D j hj hk hp
local notation "B₂" => terminalConicSecondBranch hπ data D j hj hk hp
local notation "P₁" => Iso.inv (conicFirstParameterIso (WeierstrassCurve.a₁ W₀) c ha) ≫
  conicFirstOpenImmersion (WeierstrassCurve.a₁ W₀) c
local notation "P₂" => Iso.inv (conicSecondParameterIso (WeierstrassCurve.a₁ W₀) c ha) ≫
  conicSecondOpenImmersion (WeierstrassCurve.a₁ W₀) c

/-- The full first conic meets its opposite complete terminal branch in one puncture. -/
theorem terminalConicFirstBranch_isPullback :
    IsPullback (ι ≫ pT) (s₁ ≫ i) B₂ (C ≫ g) :=
  (residueNodeConicFirstBranch_isPullback D (start + j) hk
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
    (Data.factor6 d) hp).flip.paste_vert
      (terminalNodeConicCoordinates_isPullback hπ data D j hj hk0 hk hp)

/-- The complete original first conic parameter in the actual global model. -/
def terminalConicFirstParameter := P₁ ≫ C ≫ g

/-- The complete parameter and matching terminal affine branch have exactly one puncture. -/
theorem terminalConicFirstParameter_isPullback :
    IsPullback (ι ≫ pT) p B₂ (terminalConicFirstParameter hπ data D j hj hk0 hk) := by
  have H := terminalConicFirstBranch_isPullback hπ data D j hj hk0 hk hp
  rw [conicBoundaryFirst_inclusion] at H
  have T : IsPullback (𝟙 _) p (p ≫ P₁) P₁ :=
    IsPullback.of_horiz_isIso_mono ⟨by simp only [Category.id_comp]⟩
  simpa only [Category.id_comp, Category.assoc, terminalConicFirstParameter]
    using T.paste_horiz H

/-- The original Laurent scheme is the entire matching fiber product. -/
def terminalConicFirstParameterPullbackIso :=
  (terminalConicFirstParameter_isPullback hπ data D j hj hk0 hk hp).isoPullback

/-- The full second conic meets its opposite complete terminal branch in one puncture. -/
theorem terminalConicSecondBranch_isPullback :
    IsPullback (ι ≫ pT) (s₂ ≫ i) B₁ (C ≫ g) :=
  (residueNodeConicSecondBranch_isPullback D (start + j) hk
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
    (Data.factor6 d) hp).flip.paste_vert
      (terminalNodeConicCoordinates_isPullback hπ data D j hj hk0 hk hp)

/-- The complete original second conic parameter in the actual global model. -/
def terminalConicSecondParameter := P₂ ≫ C ≫ g

/-- The complete parameter and matching terminal affine branch have exactly one puncture. -/
theorem terminalConicSecondParameter_isPullback :
    IsPullback (ι ≫ pT) p B₁ (terminalConicSecondParameter hπ data D j hj hk0 hk) := by
  have H := terminalConicSecondBranch_isPullback hπ data D j hj hk0 hk hp
  rw [conicBoundarySecond_inclusion] at H
  have T : IsPullback (𝟙 _) p (p ≫ P₂) P₂ :=
    IsPullback.of_horiz_isIso_mono ⟨by simp only [Category.id_comp]⟩
  simpa only [Category.id_comp, Category.assoc, terminalConicSecondParameter]
    using T.paste_horiz H

/-- The original Laurent scheme is the entire matching fiber product. -/
def terminalConicSecondParameterPullbackIso :=
  (terminalConicSecondParameter_isPullback hπ data D j hj hk0 hk hp).isoPullback

end FLT.Mazur.WeierstrassDividedDepth
