/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFullResidueAtlas

/-!
# The complete residue atlas after coefficient extension

The finite normalized atlas pulls back to the actual global model over an
extension of the residue field. Each member is the entire cartesian preimage
of its original normalized chart, with its original indexed inclusion and
cubic contraction. In particular this applies to geometric field extensions.
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
local notation "K" => ResidueField R
variable (S : Type u) [CommRing S] [Algebra R S] [Algebra (ResidueField R) S]
  [IsScalarTower R (ResidueField R) S] (s : ℕ) (hs : s ≤ n)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "qS" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "e" => Spec.map (CommRingCat.ofHom (algebraMap K S))
local notation "f" => finiteGlobalStructure hπ data s hs

omit [IsDomain R] [IsBezout R] in
/-- The coefficient square for an extension of the residue field commutes. -/
theorem residueExtension_coefficient : e ≫ q = qS := by
  rw [← Spec.map_comp]
  exact congrArg (fun g : R →+* S => Spec.map (CommRingCat.ofHom g))
    (IsScalarTower.algebraMap_eq R K S).symm

/-- Projection from the actual extended global model to the original residue model. -/
def globalResidueExtensionMap :
    finiteGlobalTensorModel hπ data S s hs ⟶ finiteGlobalTensorModel hπ data K s hs :=
  pullback.lift (pullback.fst qS f ≫ e) (pullback.snd qS f) (by
    rw [Category.assoc, residueExtension_coefficient, pullback.condition])

/-- Extension preserves the original residue coefficient map. -/
@[reassoc] theorem globalResidueExtensionMap_structure :
    globalResidueExtensionMap hπ data S s hs ≫ pullback.fst q f =
      pullback.fst qS f ≫ e := pullback.lift_fst _ _ _

/-- Extension preserves the whole original global modification. -/
@[reassoc] theorem globalResidueExtensionMap_projection :
    globalResidueExtensionMap hπ data S s hs ≫ pullback.snd q f =
      pullback.snd qS f := pullback.lift_snd _ _ _

/-- This is the full base change square over the residue field. -/
theorem globalResidueExtensionMap_isPullback :
    IsPullback (pullback.fst qS f) (globalResidueExtensionMap hπ data S s hs)
      e (pullback.fst q f) := by
  apply (IsPullback.paste_vert_iff (IsPullback.of_hasPullback q f)
    (globalResidueExtensionMap_structure hπ data S s hs).symm).mp
  simpa only [residueExtension_coefficient, globalResidueExtensionMap_projection] using
    (IsPullback.of_hasPullback qS f)

variable (D : SplitNodeDepth W π depth) (hdepth : 0 < depth)
  (hk : 2 * (start + s) ≤ depth)
local notation "C" => globalFullResidueOpenCover hπ data D hdepth s hs hk
local notation "p" => globalResidueExtensionMap hπ data S s hs

/-- The complete finite normalized cover of the actual coefficient-extended model. -/
def globalExtendedResidueOpenCover : (finiteGlobalTensorModel hπ data S s hs).OpenCover :=
  (C).pullback₁ p

instance globalExtendedResidueOpenCover_finite :
    Finite (globalExtendedResidueOpenCover hπ data S s hs D hdepth hk).I₀ := by
  change Finite (C).I₀
  infer_instance

/-- Every point after extension belongs to an entire pulled-back normalized chart. -/
theorem globalExtendedResidueOpenCover_covers
    (z : finiteGlobalTensorModel hπ data S s hs) :
    ∃ i x, (globalExtendedResidueOpenCover hπ data S s hs D hdepth hk).f i x = z :=
  (globalExtendedResidueOpenCover hπ data S s hs D hdepth hk).exists_eq z

/-- The chart square is cartesian, so extension cannot omit a component or branch. -/
theorem globalExtendedResidueOpenCover_isPullback (i : (C).I₀) :
    IsPullback ((globalExtendedResidueOpenCover hπ data S s hs D hdepth hk).f i)
      ((C).pullbackHom p i) p ((C).f i) := by
  exact IsPullback.of_hasPullback p ((C).f i)

/-- Every extended inclusion retains its original normalized chart map. -/
@[reassoc] theorem globalExtendedResidueOpenCover_map (i : (C).I₀) :
    (globalExtendedResidueOpenCover hπ data S s hs D hdepth hk).f i ≫ p =
      (C).pullbackHom p i ≫ (C).f i := pullback.condition

/-- Every extended normalized member keeps the actual original global index. -/
@[reassoc] theorem globalExtendedResidueOpenCover_index (i : Fin (s + 3))
    (a : (globalFullResidueAtlasRefinement hπ data D hdepth s hs hk i).I₀) :
    (globalExtendedResidueOpenCover hπ data S s hs D hdepth hk).f ⟨i, a⟩ ≫ p =
      (C).pullbackHom p ⟨i, a⟩ ≫
        (globalFullResidueAtlasRefinement hπ data D hdepth s hs hk i).f a ≫
          globalTensorAtlasMap hπ data K s hs i := by
  rw [globalExtendedResidueOpenCover_map, globalFullResidueOpenCover_map]

/-- The contraction square still uses the original integral cubic. -/
@[reassoc] theorem globalExtendedResidueOpenCover_toCurve (i : (C).I₀) :
    (globalExtendedResidueOpenCover hπ data S s hs D hdepth hk).f i ≫
      pullback.snd qS f ≫ finiteGlobalContraction hπ data s hs =
      (C).pullbackHom p i ≫ (C).f i ≫ pullback.snd q f ≫
        finiteGlobalContraction hπ data s hs := by
  rw [← globalResidueExtensionMap_projection hπ data S s hs]
  simp only [← Category.assoc, globalExtendedResidueOpenCover_map]

end FLT.Mazur.WeierstrassDividedDepth
