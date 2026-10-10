/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialGlobalTensorChart
public import FLT.Mazur.WeierstrassModificationXZeroResidueGeometry

/-!
# The entire start-zero slope chart in the projective residue model

At positive total depth the original initial tensor chart has a full slope
normal form even when the starting depth is zero. Its actual global index,
complete image, original cubic contraction and coefficient structure survive.
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
  (D : SplitNodeDepth W π depth) (hdepth : 0 < depth) (hstart : start = 0)
  (j : ℕ) (hj : j ≤ n)
open WeierstrassModificationX
local notation "K" => ResidueField R
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "e" => zeroResidueSlopeIso D hdepth start hstart
  (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀)
  (Data.factor3 d₀) (Data.factor4 d₀) (Data.factor6 d₀)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The entire slope line with both tangent factors inverted embeds in the global model. -/
def initialZeroSlopeChart : Spec (.of (SlopeOpen a)) ⟶
    finiteGlobalTensorModel hπ data K j hj :=
  (e).hom ≫ globalInitialTensorChart hπ data K j hj

instance initialZeroSlopeChart_isOpenImmersion :
    IsOpenImmersion (initialZeroSlopeChart hπ data D hdepth hstart j hj) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The slope normal form covers exactly the entire original initial chart. -/
theorem initialZeroSlopeChart_range :
    Set.range (initialZeroSlopeChart hπ data D hdepth hstart j hj) =
      Set.range (globalInitialTensorChart hπ data K j hj) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(e).hom x, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := (e).hom.homeomorph.surjective x
    exact ⟨y, congrArg (globalInitialTensorChart hπ data K j hj) hy⟩

/-- The normalized initial chart retains the full original cubic contraction. -/
@[reassoc] theorem initialZeroSlopeChart_toCurve :
    initialZeroSlopeChart hπ data D hdepth hstart j hj ≫
      pullback.snd q (finiteGlobalStructure hπ data j hj) ≫
        finiteGlobalContraction hπ data j hj =
      zeroResidueSlopeContraction D hdepth start hstart
        (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀)
        (Data.factor3 d₀) (Data.factor4 d₀) (Data.factor6 d₀) := by
  rw [initialZeroSlopeChart, Category.assoc, globalInitialTensorChart_toCurve]
  exact zeroResidueSlopeIso_contraction D hdepth start hstart
    (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀)
    (Data.factor3 d₀) (Data.factor4 d₀) (Data.factor6 d₀)

/-- The global initial slope chart retains its residue coefficient structure. -/
@[reassoc] theorem initialZeroSlopeChart_structure :
    initialZeroSlopeChart hπ data D hdepth hstart j hj ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap K (SlopeOpen a))) := by
  rw [initialZeroSlopeChart, Category.assoc, globalInitialTensorChart_structure]
  exact zeroResidueSlopeIso_structure D hdepth start hstart
    (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀)
    (Data.factor3 d₀) (Data.factor4 d₀) (Data.factor6 d₀)

/-- The full slope normal form identifies the exact last indexed atlas object. -/
def initialZeroSlopeAtlasIso : Spec (.of (SlopeOpen a)) ≅
    globalTensorAtlasObject hπ data K j hj (Fin.succ ⟨j + 1, by omega⟩) :=
  e ≪≫ finiteInitialTensorAtlasIso hπ data K j hj

/-- This indexed comparison uses the original projective inclusion. -/
@[reassoc] theorem initialZeroSlopeAtlasIso_map :
    (initialZeroSlopeAtlasIso hπ data D hdepth hstart j hj).hom ≫
      globalTensorAtlasMap hπ data K j hj (Fin.succ ⟨j + 1, by omega⟩) =
        initialZeroSlopeChart hπ data D hdepth hstart j hj := by
  change (_ ≫ _) ≫ _ = _
  rw [Category.assoc, globalInitialTensorChart_eq_index]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
