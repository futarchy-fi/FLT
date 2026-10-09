/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalZeroSuccessive
public import FLT.Mazur.WeierstrassDividedOlderGlobalTensorCharts

/-!
# The complete first horizontal fiber retained at every later global index

The scale-one spectrum and its full original contraction survive every later
modification at global index r+2. No component is discarded.
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
local notation "E" => zeroResidueFiberIso D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
/-- The full horizontal fiber as the original global successive open chart. -/
def olderGlobalZeroSuccessiveChart : Spec (.of F) ⟶
    finiteGlobalTensorModel hπ data K (j + 1 + r) hr :=
  (E).hom ≫ olderGlobalTensorChart hπ data K j hj r hr

/-- The full normalized fiber is the exact retained global atlas object. -/
def olderGlobalZeroAtlasIso : Spec (.of F) ≅
    globalTensorAtlasObject hπ data K (j + 1 + r) hr (Fin.succ ⟨r + 1, by omega⟩) :=
  E ≪≫ olderSuccessiveTensorAtlasIso hπ data K j hj r hr

/-- The complete normalized comparison keeps the actual inclusion at index r+2. -/
@[reassoc] theorem olderGlobalZeroAtlasIso_map :
    (olderGlobalZeroAtlasIso hπ data D j hj r hr hk0 hk).hom ≫
      globalTensorAtlasMap hπ data K (j + 1 + r) hr (Fin.succ ⟨r + 1, by omega⟩) =
        olderGlobalZeroSuccessiveChart hπ data D j hj r hr hk0 hk := by
  change ((E).hom ≫ _) ≫ _ = _
  rw [Category.assoc, olderGlobalTensorChart_eq_index]
  rfl

instance olderGlobalZeroSuccessiveChart_isOpenImmersion :
    IsOpenImmersion (olderGlobalZeroSuccessiveChart hπ data D j hj r hr hk0 hk) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The comparison keeps every point of the original successive atlas chart. -/
theorem olderGlobalZeroSuccessiveChart_range :
    Set.range (olderGlobalZeroSuccessiveChart hπ data D j hj r hr hk0 hk) =
      Set.range (olderGlobalTensorChart hπ data K j hj r hr) := by
  change Set.range (fun z => olderGlobalTensorChart hπ data K j hj r hr ((E).hom z)) = _
  simpa only [Function.comp_def, Scheme.Hom.homeomorph_apply] using
    (E).hom.homeomorph.surjective.range_comp (olderGlobalTensorChart hπ data K j hj r hr)

/-- The full global chart preserves the residue-field structure. -/
@[reassoc] theorem olderGlobalZeroSuccessiveChart_structure :
    olderGlobalZeroSuccessiveChart hπ data D j hj r hr hk0 hk ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
  rw [olderGlobalZeroSuccessiveChart, Category.assoc, olderGlobalTensorChart_structure]
  exact zeroResidueFiberIso_structure D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

/-- The actual global cubic contraction equals the complete displayed algebraic contraction. -/
@[reassoc] theorem olderGlobalZeroSuccessiveChart_toCurve :
    olderGlobalZeroSuccessiveChart hπ data D j hj r hr hk0 hk ≫
      pullback.snd q (finiteGlobalStructure hπ data (j + 1 + r) hr) ≫
        finiteGlobalContraction hπ data (j + 1 + r) hr =
      Spec.map (CommRingCat.ofHom
        (globalZeroSuccessiveContraction hπ data D j hj hk0 hk).toRingHom) ≫ toCurve d := by
  rw [olderGlobalZeroSuccessiveChart, Category.assoc, olderGlobalTensorChart_toCurve,
    xContraction]
  change Spec.map _ ≫ Spec.map _ ≫ (Spec.map _ ≫ Spec.map _) ≫ _ = _
  simp only [← Category.assoc, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
