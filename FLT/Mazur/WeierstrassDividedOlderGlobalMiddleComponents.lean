/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalTensorCharts
public import FLT.Mazur.WeierstrassModificationXConicGeometry
public import FLT.Mazur.WeierstrassSuccessiveXResidueMiddleComponents

/-!
# Full middle conic and ordered lines in the retained global fiber

The complete positive-depth horizontal fiber is covered by its original conic
and two ordered lines. Both rational conic parameter charts cover the retained
conic, including when its divided constant is zero.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "F" => WeierstrassModificationX.FiberCoordinate a c
open WeierstrassModificationX
local notation "ha" => D.a₁_unit.map (residue R)
local notation "g" => olderGlobalTensorChart hπ data K j hj r hr
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

local notation "C" => residueSuccessiveConicImmersion D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "L" => residueSuccessiveLineImmersion D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "W₀" => W.map (residue R)

/-- The complete original middle conic in the retained global fiber. -/
def olderGlobalMiddleConic := C ≫ g

/-- The original zero-slope horizontal line in the retained global fiber. -/
def olderGlobalMiddleFirstLine := L 0 (middle_first_root W₀) ≫ g

/-- The original opposite-slope horizontal line in the retained global fiber. -/
def olderGlobalMiddleSecondLine := L (-a) (middle_second_root W₀) ≫ g

/-- The full conic and both ordered lines cover exactly their original older chart. -/
theorem olderGlobalMiddleComponents_cover :
    Set.range (olderGlobalMiddleConic hπ data D j hj r hr hk0 hk) ∪
      (Set.range (olderGlobalMiddleFirstLine hπ data D j hj r hr hk0 hk) ∪
        Set.range (olderGlobalMiddleSecondLine hπ data D j hj r hr hk0 hk)) =
          Set.range g := by
  ext z
  constructor
  · rintro (⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩)
    · exact ⟨C p, rfl⟩
    · exact ⟨L 0 (middle_first_root W₀) p, rfl⟩
    · exact ⟨L (-a) (middle_second_root W₀) p, rfl⟩
  · rintro ⟨p, rfl⟩
    rcases residue_successive_components_cover D (start + j) hk0 hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) p with
      ⟨t, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact Or.inl ⟨t, rfl⟩
    · exact Or.inr (Or.inl ⟨t, rfl⟩)
    · exact Or.inr (Or.inr ⟨t, rfl⟩)

/-- The first rational conic parameter chart maps into the actual global fiber. -/
def olderGlobalMiddleConicFirstParameter :=
  (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c ≫
    olderGlobalMiddleConic hπ data D j hj r hr hk0 hk

/-- The second rational conic parameter chart maps into the actual global fiber. -/
def olderGlobalMiddleConicSecondParameter :=
  (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c ≫
    olderGlobalMiddleConic hπ data D j hj r hr hk0 hk

/-- The two actual parameter maps cover every point of the retained conic. -/
theorem olderGlobalMiddleConicParameters_cover :
    Set.range (olderGlobalMiddleConicFirstParameter hπ data D j hj r hr hk0 hk) ∪
      Set.range (olderGlobalMiddleConicSecondParameter hπ data D j hj r hr hk0 hk) =
        Set.range (olderGlobalMiddleConic hπ data D j hj r hr hk0 hk) := by
  ext z
  constructor
  · rintro (⟨p, rfl⟩ | ⟨p, rfl⟩)
    · exact ⟨conicFirstOpenImmersion a c ((conicFirstParameterIso a c ha).inv p), rfl⟩
    · exact ⟨conicSecondOpenImmersion a c ((conicSecondParameterIso a c ha).inv p), rfl⟩
  · rintro ⟨p, rfl⟩
    rcases conicOpenImmersions_cover a c ha p with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · obtain ⟨s, hs⟩ := (conicFirstParameterIso a c ha).inv.homeomorph.surjective t
      exact Or.inl ⟨s, congrArg (fun t => olderGlobalMiddleConic hπ data D j hj r hr hk0 hk
        (conicFirstOpenImmersion a c t)) hs⟩
    · obtain ⟨s, hs⟩ := (conicSecondParameterIso a c ha).inv.homeomorph.surjective t
      exact Or.inr ⟨s, congrArg (fun t => olderGlobalMiddleConic hπ data D j hj r hr hk0 hk
        (conicSecondOpenImmersion a c t)) hs⟩

end FLT.Mazur.WeierstrassDividedDepth
