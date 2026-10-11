/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityPolygonMap
public import FLT.Mazur.WeierstrassDividedPositiveEqualityCycleCoverage

/-!
# The canonical positive-start polygon comparison is surjective

Every point of the original finite residue model is reached through an original
complete cyclic component. This does not assert the outstanding pushout property.
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
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart (by omega) hp
local notation "N" => positiveEqualityCycleNormalization hπ data D s hs hstart (by omega) hp
local notation "Q" => positiveEqualityCycleNodes hπ data D s hs hstart (by omega)

local notation "F" => positiveEqualityCyclePolygonMap hπ data D s hs hstart hp

/-- The constructed polygon comparison reaches every point of the actual positive-start fiber. -/
theorem positiveEqualityCyclePolygonMap_surjective : Function.Surjective (F).left := by
  intro z
  obtain ⟨i, x, hx⟩ := positiveEqualityCycleComponent_cover
    hπ data D s hs hstart (by omega) hp z
  refine ⟨(PolygonPinching.componentι K (2 * s + 4) i ≫
    PolygonAtlas.normalization K (2 * s + 4)).left x, ?_⟩
  have he := congrArg Over.Hom.left
    (positiveEqualityCyclePolygonMap_component hπ data D s hs hstart hp i)
  exact (congrArg (fun q => q x) he).trans hx

end FLT.Mazur.WeierstrassDividedDepth
