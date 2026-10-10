/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalBranchIntersection
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Crossed terminal affine branches have empty conic-parameter intersections

The first parameter misses the left terminal branch and the second misses
the right. These are empty scheme fiber products, with no reducedness assumption.
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

local notation "A₁" => terminalConicFirstParameter hπ data D j hj hk0 hk
local notation "A₂" => terminalConicSecondParameter hπ data D j hj hk0 hk

/-- The whole first conic parameter misses the crossed complete terminal branch. -/
theorem terminalConicFirstParameter_cross_disjoint :
    Disjoint (Set.range A₁) (Set.range B₁) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, rfl⟩ ⟨b, hb⟩
  obtain ⟨v, _, hv⟩ := Scheme.exists_preimage_of_isPullback
    (terminalConicSecondBranch_isPullback hπ data D j hj hk0 hk hp) b (P₁ a) hb
  rw [conicBoundarySecond_inclusion] at hv
  have H := conicParameters_disjoint_of_zero W₀ c ha hc
  exact Set.disjoint_left.mp H ⟨a, rfl⟩ ⟨p v, hv⟩

/-- The crossed first-parameter fiber product is the empty scheme. -/
theorem terminalConicFirstParameter_cross_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) A₁ B₁ := by
  let _ := Scheme.isEmpty_pullback A₁ B₁
    (terminalConicFirstParameter_cross_disjoint hπ data D j hj hk0 hk hp)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback A₁ B₁)))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

/-- The whole second conic parameter misses the crossed complete terminal branch. -/
theorem terminalConicSecondParameter_cross_disjoint :
    Disjoint (Set.range A₂) (Set.range B₂) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, rfl⟩ ⟨b, hb⟩
  obtain ⟨v, _, hv⟩ := Scheme.exists_preimage_of_isPullback
    (terminalConicFirstBranch_isPullback hπ data D j hj hk0 hk hp) b (P₂ a) hb
  rw [conicBoundaryFirst_inclusion] at hv
  have H := conicParameters_disjoint_of_zero W₀ c ha hc
  exact Set.disjoint_left.mp H ⟨p v, hv⟩ ⟨a, rfl⟩

/-- The crossed second-parameter fiber product is the empty scheme. -/
theorem terminalConicSecondParameter_cross_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) A₂ B₂ := by
  let _ := Scheme.isEmpty_pullback A₂ B₂
    (terminalConicSecondParameter_cross_disjoint hπ data D j hj hk0 hk hp)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback A₂ B₂)))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

end FLT.Mazur.WeierstrassDividedDepth
