/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroSuccessive
public import FLT.Mazur.WeierstrassModificationXConicGeometry
public import FLT.Mazur.WeierstrassModificationXFiberConicGeometry

/-!
# Actual retained conic and incidence components

The complete first horizontal fiber is covered by its original incidence
line and conic. Both conic parameter charts map to the actual global model,
with all functions of the original cubic contraction retained.
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
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "F" => WeierstrassModificationX.FiberCoordinate a c
open WeierstrassModificationX
local notation "ha" => D.a₁_unit.map (residue R)
local notation "g" => olderGlobalZeroSuccessiveChart hπ data D j hj r hr hk0 hk
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The original conic component in the retained global fiber. -/
def olderGlobalZeroConic := fiberConicImmersion a c ≫ g

/-- The original incidence line in the retained global fiber. -/
def olderGlobalZeroIncidence := fiberIncidenceImmersion a c ≫ g

/-- The two original closed components cover the entire retained horizontal chart. -/
theorem olderGlobalZeroComponents_cover :
    Set.range (olderGlobalZeroIncidence hπ data D j hj r hr hk0 hk) ∪
      Set.range (olderGlobalZeroConic hπ data D j hj r hr hk0 hk) =
        Set.range (olderGlobalTensorChart hπ data K j hj r hr) := by
  rw [← olderGlobalZeroSuccessiveChart_range hπ data D j hj r hr hk0 hk]
  ext z
  constructor
  · rintro (⟨p, rfl⟩ | ⟨p, rfl⟩)
    · exact ⟨fiberIncidenceImmersion a c p, rfl⟩
    · exact ⟨fiberConicImmersion a c p, rfl⟩
  · rintro ⟨p, rfl⟩
    rcases fiber_incidence_conic_cover a c p with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact Or.inl ⟨t, rfl⟩
    · exact Or.inr ⟨t, rfl⟩

/-- The first rational conic parameter chart maps into the actual global fiber. -/
def olderGlobalZeroConicFirstParameter :=
  (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c ≫
    olderGlobalZeroConic hπ data D j hj r hr hk0 hk

/-- The second rational conic parameter chart maps into the actual global fiber. -/
def olderGlobalZeroConicSecondParameter :=
  (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c ≫
    olderGlobalZeroConic hπ data D j hj r hr hk0 hk

/-- The two actual parameter maps cover every point of the retained conic. -/
theorem olderGlobalZeroConicParameters_cover :
    Set.range (olderGlobalZeroConicFirstParameter hπ data D j hj r hr hk0 hk) ∪
      Set.range (olderGlobalZeroConicSecondParameter hπ data D j hj r hr hk0 hk) =
        Set.range (olderGlobalZeroConic hπ data D j hj r hr hk0 hk) := by
  ext z
  constructor
  · rintro (⟨p, rfl⟩ | ⟨p, rfl⟩)
    · exact ⟨conicFirstOpenImmersion a c ((conicFirstParameterIso a c ha).inv p), rfl⟩
    · exact ⟨conicSecondOpenImmersion a c ((conicSecondParameterIso a c ha).inv p), rfl⟩
  · rintro ⟨p, rfl⟩
    rcases conicOpenImmersions_cover a c ha p with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · obtain ⟨s, hs⟩ := (conicFirstParameterIso a c ha).inv.homeomorph.surjective t
      exact Or.inl ⟨s, congrArg (fun t => olderGlobalZeroConic hπ data D j hj r hr hk0 hk
        (conicFirstOpenImmersion a c t)) hs⟩
    · obtain ⟨s, hs⟩ := (conicSecondParameterIso a c ha).inv.homeomorph.surjective t
      exact Or.inr ⟨s, congrArg (fun t => olderGlobalZeroConic hπ data D j hj r hr hk0 hk
        (conicSecondOpenImmersion a c t)) hs⟩

/-- The conic map keeps the original residue-field structure. -/
@[reassoc] theorem olderGlobalZeroConic_structure :
    olderGlobalZeroConic hπ data D j hj r hr hk0 hk ≫ pullback.fst _ _ =
      conicStructure a c := by
  rw [olderGlobalZeroConic, Category.assoc, olderGlobalZeroSuccessiveChart_structure]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (fiberConicMap a c).commutes)

/-- Every original cubic function on the conic is retained by the actual global contraction. -/
@[reassoc] theorem olderGlobalZeroConic_toCurve :
    olderGlobalZeroConic hπ data D j hj r hr hk0 hk ≫
      pullback.snd q (finiteGlobalStructure hπ data (j + 1 + r) hr) ≫
        finiteGlobalContraction hπ data (j + 1 + r) hr =
      fiberConicImmersion a c ≫ Spec.map (CommRingCat.ofHom
        (globalZeroSuccessiveContraction hπ data D j hj hk0 hk).toRingHom) ≫ toCurve d := by
  rw [olderGlobalZeroConic, Category.assoc, olderGlobalZeroSuccessiveChart_toCurve]

/-- Every original cubic function on the incidence line is retained as well. -/
@[reassoc] theorem olderGlobalZeroIncidence_toCurve :
    olderGlobalZeroIncidence hπ data D j hj r hr hk0 hk ≫
      pullback.snd q (finiteGlobalStructure hπ data (j + 1 + r) hr) ≫
        finiteGlobalContraction hπ data (j + 1 + r) hr =
      fiberIncidenceImmersion a c ≫ Spec.map (CommRingCat.ofHom
        (globalZeroSuccessiveContraction hπ data D j hj hk0 hk).toRingHom) ≫ toCurve d := by
  rw [olderGlobalZeroIncidence, Category.assoc, olderGlobalZeroSuccessiveChart_toCurve]

end FLT.Mazur.WeierstrassDividedDepth
