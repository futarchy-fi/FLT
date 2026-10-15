/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedRetainedIndexComparison
public import FLT.Mazur.EllipticRetainedFinalCyclicCoordinates

/-!
# Natural retained arithmetic labels in the original complete component cycles

The W308 smooth charts agree with the actual odd and even cyclic components,
with arbitrary residue-unit scale corrections. Only stage-index equality is used.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (r : (ResidueField A)ˣ) (s : ℕ) (he : depth / 2 = s + 1) (j : Fin s)
local notation "F" => ResidueField A
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "data" => splitResolutionData A D
local notation "p" => resolvedSplitStructure A D
local notation "m" => s - (j.val + 1)
local notation "t" => eqToHom (finiteGlobalTensorModel_index_congr hπ data F
  (le_refl _) (by omega) he)
local notation "t₀" => eqToHom (finiteGlobalTensorModel_index_congr hπ data F (b := s + 1)
  (a := j.val + 2 + m) (by omega) (by omega) (by omega))
local notation "a" => nodeLaurentScale D r (0 + (j.val + 1))
local notation "pos" => retainedTrivializedPositiveChart A hπ data D r (j.val + 1)
  (by omega) m (by omega) (by omega) (by omega)
local notation "neg" => retainedTrivializedNegativeChart A hπ data D r (j.val + 1)
  (by omega) m (by omega) (by omega) (by omega)
local notation "torus" => Over.Hom.left (PolygonPinching.torusToComponent F)
local notation "P" => resolvedOrientedComponentChart A D r (Fin.mk (j.val + 1) (by omega))
local notation "N" => resolvedOrientedComponentChart A D r
  (Fin.mk (depth - (j.val + 1)) (by omega))

/-- The actual positive smooth chart agrees with its retained presentation at the final stage. -/
@[reassoc] theorem resolvedOrientedComponentChart_retainedPositive_stage :
    P ≫ (p).smoothLocus.ι ≫ t = pos ≫ t₀ := by
  rw [resolvedOrientedComponentChart_retainedPositive_assoc A D r
    (j.val + 1) (by omega) (by omega)]
  apply eq_of_heq
  exact (comp_eqToHom_heq _ _).trans
    ((resolvedRetainedPositiveChart_original_heq A D r (j.val + 1)
      (by omega) (by omega) m (by omega)).trans (comp_eqToHom_heq _ _).symm)

/-- The original negative smooth chart agrees with its full retained final-stage presentation. -/
@[reassoc] theorem resolvedOrientedComponentChart_retainedNegative_stage :
    N ≫ (p).smoothLocus.ι ≫ t = neg ≫ t₀ := by
  rw [resolvedOrientedComponentChart_retainedNegative_assoc A D r
    (j.val + 1) (by omega) (by omega)]
  apply eq_of_heq
  exact (comp_eqToHom_heq _ _).trans
    ((resolvedRetainedNegativeChart_original_heq A D r (j.val + 1)
      (by omega) (by omega) m (by omega)).trans (comp_eqToHom_heq _ _).symm)

/-- The positive W308 retained label maps into its original odd cyclic component. -/
@[reassoc] theorem resolvedOrientedComponentChart_oddRetainedPositive_cyclic
    (hp : 2 * (s + 1) < depth) :
    P ≫ (p).smoothLocus.ι ≫ t =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling a).toRingHom) ≫
        torus ≫ (zeroSplitCycleComponent hπ data D s (by omega) rfl
          (by omega) (by omega) ⟨j.val + 1, by omega⟩).left := by
  rw [resolvedOrientedComponentChart_retainedPositive_stage A D r s he j]
  exact retainedTrivializedPositiveChart_odd_cyclic A hπ data D r s
    (by omega) (by omega) j rfl (by omega)

/-- The complementary W308 retained label keeps its signed inverse odd cyclic coordinate. -/
@[reassoc] theorem resolvedOrientedComponentChart_oddRetainedNegative_cyclic
    (hp : depth = 2 * s + 3) :
    N ≫ (p).smoothLocus.ι ≫ t =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling (-a)⁻¹).toRingHom) ≫
        torus ≫ (zeroSplitCycleComponent hπ data D s (by omega) rfl
          (by omega) (by omega) ⟨depth - (j.val + 1), by omega⟩).left := by
  rw [resolvedOrientedComponentChart_retainedNegative_stage A D r s he j]
  have hi : (⟨depth - (j.val + 1), by omega⟩ : Fin (2 * s + 3)) =
      ⟨2 * s + 2 - j.val, by omega⟩ := by
    apply Fin.ext
    change depth - (j.val + 1) = 2 * s + 2 - j.val
    omega
  rw [hi]
  exact retainedTrivializedNegativeChart_odd_cyclic A hπ data D r s
    (by omega) (by omega) j rfl (by omega)

/-- The positive W308 retained label keeps its original even cyclic coordinate. -/
@[reassoc] theorem resolvedOrientedComponentChart_evenRetainedPositive_cyclic
    (hp : 2 * (s + 1) = depth) :
    P ≫ (p).smoothLocus.ι ≫ t =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling a).toRingHom) ≫
        torus ≫ (zeroEqualityCycleComponent hπ data D s (by omega) rfl
          (by omega) (by omega) ⟨j.val + 1, by omega⟩).left := by
  rw [resolvedOrientedComponentChart_retainedPositive_stage A D r s he j]
  exact retainedTrivializedPositiveChart_even_cyclic A hπ data D r s
    (by omega) (by omega) j rfl (by omega)

/-- The complementary W308 retained label keeps its signed inverse even cyclic coordinate. -/
@[reassoc] theorem resolvedOrientedComponentChart_evenRetainedNegative_cyclic
    (hp : 2 * (s + 1) = depth) :
    N ≫ (p).smoothLocus.ι ≫ t =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling (-a)⁻¹).toRingHom) ≫
        torus ≫ (zeroEqualityCycleComponent hπ data D s (by omega) rfl
          (by omega) (by omega) ⟨depth - (j.val + 1), by omega⟩).left := by
  rw [resolvedOrientedComponentChart_retainedNegative_stage A D r s he j]
  have hi : (⟨depth - (j.val + 1), by omega⟩ : Fin (2 * s + 2)) =
      ⟨2 * s + 1 - j.val, by omega⟩ := by
    apply Fin.ext
    change depth - (j.val + 1) = 2 * s + 1 - j.val
    omega
  rw [hi]
  exact retainedTrivializedNegativeChart_even_cyclic A hπ data D r s
    (by omega) (by omega) j rfl (by omega)

end FLT.Mazur.WeierstrassDividedDepth
