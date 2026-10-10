/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXZeroContraction
public import FLT.Mazur.WeierstrassDividedGlobalTensorCharts

/-!
# The first horizontal residue fiber inside the global model

The full scale-one comparison is an actual global open chart. Its image is
exactly the original successive tensor chart, and its contraction retains
all functions on the preceding integral divided chart.
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
local notation "f" => zeroResiduePreviousMap D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "A" => WeierstrassDilatation.Coordinate W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "p" => WeierstrassDilatation.parameterEquiv W (π ^ (start + j))
  (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (π * Data.b3 e) (π * Data.b4 e) (π ^ 2 * Data.b6 e) rfl
  (factor3_step hπ d e) (factor4_step hπ d e) (factor6_step hπ d e)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "t" => WeierstrassModificationX.fiberT a c
local notation "v" => WeierstrassModificationX.fiberV a c
local notation "u" => v * (v + algebraMap K F a) - algebraMap K F c * t ^ 2

/-- The full horizontal fiber as the original global successive open chart. -/
def globalZeroSuccessiveChart : Spec (.of F) ⟶
    finiteGlobalTensorModel hπ data K (j + 1) hj :=
  (E).hom ≫ globalSuccessiveTensorChart hπ data K j hj

instance globalZeroSuccessiveChart_isOpenImmersion :
    IsOpenImmersion (globalZeroSuccessiveChart hπ data D j hj hk0 hk) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The comparison keeps every point of the original successive atlas chart. -/
theorem globalZeroSuccessiveChart_range :
    Set.range (globalZeroSuccessiveChart hπ data D j hj hk0 hk) =
      Set.range (globalSuccessiveTensorChart hπ data K j hj) := by
  change Set.range (fun z => globalSuccessiveTensorChart hπ data K j hj ((E).hom z)) = _
  simpa only [Function.comp_def, Scheme.Hom.homeomorph_apply] using
    (E).hom.homeomorph.surjective.range_comp (globalSuccessiveTensorChart hπ data K j hj)

/-- The full global chart preserves the residue-field structure. -/
@[reassoc] theorem globalZeroSuccessiveChart_structure :
    globalZeroSuccessiveChart hπ data D j hj hk0 hk ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
  rw [globalZeroSuccessiveChart, Category.assoc, globalSuccessiveTensorChart_structure]
  exact zeroResidueFiberIso_structure D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

/-- The contraction on all functions of the actual preceding integral atlas chart. -/
def globalZeroSuccessiveContraction : A →ₐ[R] F := (f).comp (p).toAlgHom

omit [IsBezout R] in
/-- The global contraction retains the full horizontal polynomial. -/
theorem globalZeroSuccessiveContraction_x :
    globalZeroSuccessiveContraction hπ data D j hj hk0 hk
      (WeierstrassDilatation.x W (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d)) =
        u := by
  change f (p _) = _
  rw [WeierstrassDilatation.parameterEquiv_x, zeroResiduePreviousMap_x]

omit [IsBezout R] in
/-- The global contraction retains the original vertical coordinate on every component. -/
theorem globalZeroSuccessiveContraction_y :
    globalZeroSuccessiveContraction hπ data D j hj hk0 hk
      (WeierstrassDilatation.y W (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d)) =
        u * v := by
  change f (p _) = _
  rw [WeierstrassDilatation.parameterEquiv_y, zeroResiduePreviousMap_y]

/-- The actual global cubic contraction equals the complete displayed algebraic contraction. -/
@[reassoc] theorem globalZeroSuccessiveChart_toCurve :
    globalZeroSuccessiveChart hπ data D j hj hk0 hk ≫
      pullback.snd q (finiteGlobalStructure hπ data (j + 1) hj) ≫
        finiteGlobalContraction hπ data (j + 1) hj =
      Spec.map (CommRingCat.ofHom
        (globalZeroSuccessiveContraction hπ data D j hj hk0 hk).toRingHom) ≫ toCurve d := by
  rw [globalZeroSuccessiveChart, Category.assoc, globalSuccessiveTensorChart_toCurve,
    xContraction]
  change Spec.map _ ≫ Spec.map _ ≫ (Spec.map _ ≫ Spec.map _) ≫ _ = _
  simp only [← Category.assoc, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
