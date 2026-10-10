/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicIncidencePreimage
public import FLT.Mazur.WeierstrassDividedZeroExteriorCoverage
public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroNodeBoundaries

/-!
# Exact exterior intersections with the original two conic parameters

The full exterior, including infinity, meets each complete parameter only at
its original ordered node. No split-constant hypothesis is needed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Injective common postcomposition preserves the exact parameter preimage of an image. -/
theorem componentPreimage_postcomp {A B X Y : Scheme.{u}} (f : A ⟶ X) (g : B ⟶ X)
    (t : X ⟶ Y) (ht : Function.Injective t) :
    (g ≫ t) ⁻¹' Set.range (f ≫ t) = g ⁻¹' Set.range f := by
  change (t ∘ g) ⁻¹' Set.range (t ∘ f) = _
  rw [Set.range_comp, Set.preimage_comp, Set.preimage_image_eq _ ht]

/-- An exact parameter preimage identifies the full intersection of the two images. -/
theorem componentRange_inter_of_preimage {A B C X : Scheme.{u}}
    (f : A ⟶ X) (g : B ⟶ X) (o : C ⟶ B)
    (h : g ⁻¹' Set.range f = Set.range o) :
    Set.range f ∩ Set.range g = Set.range (o ≫ g) := by
  ext z
  constructor
  · rintro ⟨hf, y, rfl⟩
    obtain ⟨x, rfl⟩ := (Set.ext_iff.mp h y).mp hf
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(Set.ext_iff.mp h (o x)).mpr ⟨x, rfl⟩, ⟨o x, rfl⟩⟩

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "g" => olderGlobalZeroSuccessiveChart hπ data D j hj r hr hk0 hk
local notation "E" => zeroRetainedExteriorToGlobal hπ data D j hj r hr hk0 hk
local notation "O" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicParameterOrigin c)))

/-- The first full conic parameter meets the complete exterior only at its original origin. -/
theorem zeroRetainedExterior_first_parameter_preimage :
    olderGlobalZeroConicFirstParameter hπ data D j hj r hr hk0 hk ⁻¹' Set.range E =
      Set.range O := by
  rw [zeroRetainedExteriorToGlobal_range, Set.preimage_union]
  have hi : olderGlobalZeroConicFirstParameter hπ data D j hj r hr hk0 hk ⁻¹'
      Set.range (finiteInfinityTensorChart hπ data K (j + 1 + r) hr) = ∅ := by
    rw [olderGlobalZeroConicFirstParameter, chart_comp_preimage, chart_comp_preimage,
      olderGlobalZeroConic_infinity_preimage_empty, Set.preimage_empty, Set.preimage_empty]
  rw [hi, Set.union_empty]
  unfold olderGlobalZeroConicFirstParameter olderGlobalZeroConic olderGlobalZeroIncidence
  rw [← Category.assoc _ _ g, ← Category.assoc _ _ g,
    componentPreimage_postcomp _ _ g (g).isOpenEmbedding.injective]
  exact conicFirstParameter_incidence_preimage a c ha

/-- The second full parameter retains its distinct original incidence marking. -/
theorem zeroRetainedExterior_second_parameter_preimage :
    olderGlobalZeroConicSecondParameter hπ data D j hj r hr hk0 hk ⁻¹' Set.range E =
      Set.range O := by
  rw [zeroRetainedExteriorToGlobal_range, Set.preimage_union]
  have hi : olderGlobalZeroConicSecondParameter hπ data D j hj r hr hk0 hk ⁻¹'
      Set.range (finiteInfinityTensorChart hπ data K (j + 1 + r) hr) = ∅ := by
    rw [olderGlobalZeroConicSecondParameter, chart_comp_preimage, chart_comp_preimage,
      olderGlobalZeroConic_infinity_preimage_empty, Set.preimage_empty, Set.preimage_empty]
  rw [hi, Set.union_empty]
  unfold olderGlobalZeroConicSecondParameter olderGlobalZeroConic olderGlobalZeroIncidence
  rw [← Category.assoc _ _ g, ← Category.assoc _ _ g,
    componentPreimage_postcomp _ _ g (g).isOpenEmbedding.injective]
  exact conicSecondParameter_incidence_preimage a c ha

/-- The exterior and first original full parameter intersect exactly in the first node. -/
theorem zeroRetainedExterior_first_parameter_inter :
    Set.range E ∩
        Set.range (olderGlobalZeroConicFirstParameter hπ data D j hj r hr hk0 hk) =
      Set.range (olderGlobalZeroFirstSection hπ data D j hj r hr hk0 hk) := by
  rw [componentRange_inter_of_preimage E _ O
    (zeroRetainedExterior_first_parameter_preimage hπ data D j hj r hr hk0 hk),
    olderGlobalZeroConicFirstParameter_origin]

/-- The exterior and second original full parameter intersect exactly in the opposite node. -/
theorem zeroRetainedExterior_second_parameter_inter :
    Set.range E ∩
        Set.range (olderGlobalZeroConicSecondParameter hπ data D j hj r hr hk0 hk) =
      Set.range (olderGlobalZeroSecondSection hπ data D j hj r hr hk0 hk) := by
  rw [componentRange_inter_of_preimage E _ O
    (zeroRetainedExterior_second_parameter_preimage hπ data D j hj r hr hk0 hk),
    olderGlobalZeroConicSecondParameter_origin]

end FLT.Mazur.WeierstrassDividedDepth
