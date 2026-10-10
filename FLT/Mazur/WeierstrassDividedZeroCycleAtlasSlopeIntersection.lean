/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleZeroIndexedMap
public import FLT.Mazur.WeierstrassDividedZeroIncidenceInfinity
public import FLT.Mazur.WeierstrassDividedFinalZeroExteriorRanges

/-!
# The full oldest-chart and infinity intersection at the fixed cyclic stage

The actual punctured slope scheme is transported with both original incidence
maps to the fixed global atlas. It is the entire categorical fiber product.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "α" => residue R W.a₁
local notation "c" => residue R (Data.b6 (data (Fin.mk 1 (by omega))))
local notation "v" => olderGlobalZeroAtlasIso hπ data D 0 (by omega) s (by omega)
  (by omega) (by omega)
local notation "transport" => eqToIso (globalTensorAtlasObject_index_congr hπ data
  (a := 0 + 1 + s) (by omega) hs (by omega)
  (Fin.succ (Fin.mk (s + 1) (by omega))) (Fin.mk (s + 2) (by omega)) (by rfl))
local notation "target" => eqToIso (finiteGlobalTensorModel_index_congr hπ data K
  (a := 0 + 1 + s) (by omega) hs (by omega))
local notation "q" => olderGlobalZeroSlopeToInfinity hπ data D 0 (by omega) s
  (by omega) (by omega) (by omega)
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs

/-- The original whole slope boundary maps to the oldest fixed atlas object. -/
def zeroSplitCycleSlopeToZeroAtlas : Spec (.of (SlopeOpen α)) ⟶
    globalTensorAtlasObject hπ data K (s + 1) hs ⟨s + 2, by omega⟩ :=
  fiberExteriorSlopeChart α c ≫ (v).hom ≫ (transport).hom

/-- The two original full boundary maps form the actual fixed-atlas pullback square. -/
theorem zeroSplitCycleSlopeAtlas_isPullback :
    IsPullback q (zeroSplitCycleSlopeToZeroAtlas hπ data D s hs hstart hk)
      (m 0) (m ⟨s + 2, by omega⟩) := by
  let V := v ≪≫ transport
  apply (zeroRetainedSlopeInfinity_isPullback hπ data D 0 (by omega) s
    (by omega) (by omega) (by omega)).of_iso
      (Iso.refl _) (Iso.refl _) V target
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, V, Iso.trans_hom,
      zeroSplitCycleSlopeToZeroAtlas, Category.assoc]
    rw [← fiberExteriorSlopeChart_incidence]
    simp only [Category.assoc, PrincipalOpenTransport.inclusion]
  · simp only [Iso.refl_hom, Category.id_comp, eqToIso.hom]
    exact finiteInfinityTensorChart_index_transport hπ data _ hs (by omega)
  · dsimp only [V, Iso.trans_hom, eqToIso.hom]
    rw [Category.assoc, globalTensorAtlasMap_index_transport hπ data
      (a := 0 + 1 + s) (by omega) hs (by omega) _ _ (by rfl),
      ← Category.assoc, olderGlobalZeroAtlasIso_map]

/-- The slope boundary preserves both global atlas maps after the stage transport. -/
@[reassoc] theorem zeroSplitCycleSlopeToZeroAtlas_global :
    zeroSplitCycleSlopeToZeroAtlas hπ data D s hs hstart hk ≫ m ⟨s + 2, by omega⟩ =
      q ≫ m 0 :=
  (zeroSplitCycleSlopeAtlas_isPullback hπ data D s hs hstart hk).w.symm

/-- The entire actual infinity/oldest-chart intersection is the original slope scheme. -/
def zeroSplitCycleSlopeAtlasPullbackIso : Spec (.of (SlopeOpen α)) ≅
    Limits.pullback (m 0) (m ⟨s + 2, by omega⟩) :=
  (zeroSplitCycleSlopeAtlas_isPullback hπ data D s hs hstart hk).isoPullback

end FLT.Mazur.WeierstrassDividedDepth
