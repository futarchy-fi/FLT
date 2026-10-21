/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTensorIntegralAtlas
public import FLT.Mazur.WeierstrassDividedGlobalFiniteFlat
public import FLT.Mazur.SchemeSmoothLocusCartesian

/-!
# Full indexed smooth domains agree with relative smoothness after scalar extension

Flatness identifies the inverse image of the integral smooth locus with the
entire relative smooth locus. In particular, residue boundary coverage applies
to the exact indexed smooth domains used by the integral atlas transitions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (j : ℕ) (hj : j ≤ n)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "projection" => pullback.snd q base
local notation "structure" => pullback.fst q base
local notation "chart" => globalTensorAtlasMap hπ data S j hj

/-- Relative smoothness of the full coefficient model is exactly integral smoothness. -/
theorem tensorGlobalRelativeSmooth_eq :
    projection ⁻¹ᵁ (base).smoothLocus = (structure).smoothLocus :=
  smoothLocus_preimage_of_isPullback (IsPullback.of_hasPullback q base).flip

/-- Every indexed full smooth domain equals the whole relative smooth preimage. -/
theorem tensorIntegralAtlasSmoothOpen_relative (a : Fin (j + 3)) :
    tensorIntegralAtlasSmoothOpen hπ data S j hj a =
      chart a ⁻¹ᵁ (structure).smoothLocus := by
  rw [tensorIntegralAtlasSmoothOpen_eq, Scheme.Hom.comp_preimage,
    tensorGlobalRelativeSmooth_eq]

/-- Membership in the indexed smooth domain detects relative smoothness of its actual input. -/
theorem tensorIntegralAtlasSmoothOpen_mem_relative (a : Fin (j + 3))
    (p : globalTensorAtlasObject hπ data S j hj a) :
    p ∈ tensorIntegralAtlasSmoothOpen hπ data S j hj a ↔
      chart a p ∈ (structure).smoothLocus := by
  rw [tensorIntegralAtlasSmoothOpen_relative]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
