/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalExterior
public import FLT.Mazur.WeierstrassDividedOlderGlobalInfinityIntersection

/-!
# Full intersections at the precise retained global atlas index

The original horizontal and infinity localizations are cartesian against
the actual atlas map at index r+2, with the canonical original source iso.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S]
  (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "u" => WeierstrassSuccessiveX.coord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "v" => olderSuccessiveTensorAtlasIso hπ data S j hj r hr
local notation "a" => globalTensorAtlasMap hπ data S (j + 1 + r) hr
  (Fin.succ (Fin.mk (r + 1) (by omega)))
local notation "i" => olderGlobalExteriorTensorChart hπ data S j hj r hr
local notation "inf" => globalTensorAtlasMap hπ data S (j + 1 + r) hr 0

/-- The full preceding boundary is cartesian at the precise retained global atlas index. -/
theorem olderIndexedExterior_isPullback :
    IsPullback (olderGlobalHorizontalToExterior hπ data S j hj r hr)
      (PrincipalOpenTensor.inclusion S u ≫ (v).hom) i a := by
  apply (olderGlobalExteriorTensor_isPullback hπ data S j hj r hr).of_iso
    (Iso.refl _) (Iso.refl _) v (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (olderGlobalTensorChart_eq_index hπ data S j hj r hr).symm

/-- No extra points of the retained indexed atlas object meet the preceding exterior. -/
theorem olderIndexedExterior_preimage :
    a ⁻¹' Set.range i = Set.range (PrincipalOpenTensor.inclusion S u ≫ (v).hom) := by
  have H := olderIndexedExterior_isPullback hπ data S j hj r hr
  ext z
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨p, _, hp⟩ := Scheme.exists_preimage_of_isPullback H w z hw
    exact ⟨p, hp⟩
  · rintro ⟨p, rfl⟩
    exact ⟨olderGlobalHorizontalToExterior hπ data S j hj r hr p,
      congrArg (fun f => f p) H.w⟩

/-- The full infinity attachment is cartesian between actual atlas indices zero and r+2. -/
theorem olderIndexedInfinity_isPullback :
    IsPullback (olderGlobalYToInfinity hπ data S j hj r hr)
      (PrincipalOpenTensor.inclusion S (successiveOriginalY e) ≫ (v).hom) inf a := by
  apply (olderGlobalTensor_infinity_isPullback hπ data S j hj r hr).of_iso
    (Iso.refl _) (Iso.refl _) v (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (olderGlobalTensorChart_eq_index hπ data S j hj r hr).symm

/-- Infinity has exactly the original y localization as its precise indexed-chart preimage. -/
theorem olderIndexedInfinity_preimage :
    a ⁻¹' Set.range inf =
      Set.range (PrincipalOpenTensor.inclusion S (successiveOriginalY e) ≫ (v).hom) := by
  have H := olderIndexedInfinity_isPullback hπ data S j hj r hr
  ext z
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨p, _, hp⟩ := Scheme.exists_preimage_of_isPullback H w z hw
    exact ⟨p, hp⟩
  · rintro ⟨p, rfl⟩
    exact ⟨olderGlobalYToInfinity hπ data S j hj r hr p, congrArg (fun f => f p) H.w⟩

end FLT.Mazur.WeierstrassDividedDepth
