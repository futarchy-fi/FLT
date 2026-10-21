/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentTensorIndex
public import FLT.Mazur.WeierstrassDividedTensorIntegralRelativeSmooth

/-!
# Full smoothness on the canonical adjacent tensor source

The canonical retained isomorphism identifies the entire indexed integral
smooth domain with relative smoothness of the original adjacent input.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  retainedTensorAtlasIso finiteTensorAtlasObject globalSmoothAtlasOpen
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "iso" => retainedTensorAtlasIso hπ data S (j + 2 + r) hr j (by omega)
local notation "idx" => (Fin.succ ⟨j + 2 + r - j, by omega⟩ : Fin (j + 2 + r + 3))
local notation "old" => adjacentRetainedOldGlobalTensorChart hπ data S j hj r hr
local notation "s" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
  (finiteGlobalStructure hπ data (j + 2 + r) hr)

/-- No smoothness condition is added or lost by the canonical source isomorphism. -/
theorem retainedTensorAtlasIso_adjacent_smoothOpen :
    (iso).hom ⁻¹ᵁ tensorIntegralAtlasSmoothOpen hπ data S (j + 2 + r) hr idx =
      old ⁻¹ᵁ (s).smoothLocus := by
  rw [tensorIntegralAtlasSmoothOpen_relative, ← Scheme.Hom.comp_preimage,
    retainedTensorAtlasIso_adjacent_map]

end FLT.Mazur.WeierstrassDividedDepth
