/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstActionInput
public import FLT.Mazur.WeierstrassModifiedSmoothAffineRefinement

/-!
# Simultaneous fraction-input and divided-output action domains

Pull back the genuine stage-zero action along an actual first-successor
fraction input and the normalized divided output. Affine opens cover this
entire simultaneous domain. Their input projections are flat by smooth
base change and open immersion, including over the exceptional fiber.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hn : 1 ≤ n)
  (f : WeierstrassDilatation.Coordinate W (π ^ (start + 0))
    (π * (data ⟨1, Nat.lt_succ_of_le hn⟩).b3)
    (π * (data ⟨1, Nat.lt_succ_of_le hn⟩).b4)
    (π ^ 2 * (data ⟨1, Nat.lt_succ_of_le hn⟩).b6))
  (hf : f ∈ WeierstrassSuccessiveX.modificationCenter W (π ^ (start + 0)) π
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b3
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b4
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b6)
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le hn))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + 0))
  (π * (Data.b3 e)) (π * (Data.b4 e)) (π ^ 2 * (Data.b6 e))
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + 0)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "C" => BlowupFractionChart.chart I f
local notation "c" => finiteSuccessiveFractionChart hπ data 0 hn f hf
local notation "v" => finiteNormalizedChart hπ data 0 hn

/-- The full smooth product of the actual successor fraction input. -/
abbrev firstFractionProduct := pullback (integralSmoothStructure W)
  (c ≫ finiteGlobalStructure hπ data 1 hn)

/-- Include the fraction input in the whole prescribed successor action source. -/
def firstFractionInput : firstFractionProduct hπ data hn f hf ⟶
    finiteGlobalActionProduct hπ data 1 hn :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ c)
    (by rw [Category.assoc]; exact pullback.condition)

/-- The actual stage-zero action on the complete fraction-input product. -/
def firstFractionOutput : firstFractionProduct hπ data hn f hf ⟶
    finiteGlobalModel hπ data 0 (Nat.zero_le n) :=
  firstFractionInput hπ data hn f hf ≫ firstActionOutput hπ data hn

/-- The simultaneous domain of this fraction input and the normalized divided output. -/
abbrev firstFractionDomain := pullback (firstFractionOutput hπ data hn f hf) v

/-- A genuine affine atlas of the entire simultaneous input/output domain. -/
def firstFractionCover : (firstFractionDomain hπ data hn f hf).AffineOpenCover :=
  (firstFractionDomain hπ data hn f hf).affineOpenCover

/-- The actual smooth parameter on each affine presentation. -/
def firstFractionParameter (i : (firstFractionCover hπ data hn f hf).I₀) :
    Spec ((firstFractionCover hπ data hn f hf).X i) ⟶ (integralSmoothOpen W).toScheme :=
  (firstFractionCover hπ data hn f hf).f i ≫ pullback.fst _ _ ≫ pullback.fst _ _

/-- The input projection lands in the actual fraction algebra, without localizing the scale. -/
def firstFractionProjection (i : (firstFractionCover hπ data hn f hf).I₀) :
    Spec ((firstFractionCover hπ data hn f hf).X i) ⟶ Spec (.of C) :=
  (firstFractionCover hπ data hn f hf).f i ≫ pullback.fst _ _ ≫ pullback.snd _ _

/-- The output projection lands in the actual normalized divided chart. -/
def firstFractionDividedOutput (i : (firstFractionCover hπ data hn f hf).I₀) :
    Spec ((firstFractionCover hπ data hn f hf).X i) ⟶ Spec (.of B) :=
  (firstFractionCover hπ data hn f hf).f i ≫ pullback.snd _ _

/-- Each actual affine input projection is flat. -/
instance firstFractionProjection_flat (i : (firstFractionCover hπ data hn f hf).I₀) :
    Flat (firstFractionProjection hπ data hn f hf i) := by
  unfold firstFractionProjection
  infer_instance

/-- The extracted fraction-input ring map on the actual affine atlas. -/
def firstFractionHom (i : (firstFractionCover hπ data hn f hf).I₀) :
    C →+* (firstFractionCover hπ data hn f hf).X i :=
  affineChartRingHom (firstFractionProjection hπ data hn f hf i)

/-- Extraction preserves the actual fraction-input projection. -/
@[simp] theorem firstFractionHom_spec (i : (firstFractionCover hπ data hn f hf).I₀) :
    Spec.map (CommRingCat.ofHom (firstFractionHom hπ data hn f hf i)) =
      firstFractionProjection hπ data hn f hf i := affineChartRingHom_spec _

/-- The required ring flatness is derived for every member of the constructed atlas. -/
theorem firstFractionHom_flat (i : (firstFractionCover hπ data hn f hf).I₀) :
    RingHom.Flat (firstFractionHom hπ data hn f hf i) := by
  apply (Flat.SpecMap_iff (f := CommRingCat.ofHom
    (firstFractionHom hπ data hn f hf i))).mp
  rw [firstFractionHom_spec]
  infer_instance

/-- No point of the simultaneous domain is omitted from its affine presentations. -/
theorem firstFractionCover_covers (z : firstFractionDomain hπ data hn f hf) :
    ∃ i x, (firstFractionCover hπ data hn f hf).f i x = z :=
  (firstFractionCover hπ data hn f hf).openCover.exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
