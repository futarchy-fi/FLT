/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalZeroExterior
public import FLT.Mazur.WeierstrassDividedFinalChainCoverage

/-!
# The complete first retained chart and infinity in the fixed component images

The original exterior together with the entire first conic exhausts precisely
these two original chart images, including at the first positive stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
/-- Postcomposition preserves an exact equality between two unions of map images. -/
theorem componentRange_pair_eq_postcomp {A B C E X Y : Scheme.{u}}
    (f : A ⟶ X) (g : B ⟶ X) (h : C ⟶ X) (e : E ⟶ X) (t : X ⟶ Y)
    (he : Set.range f ∪ Set.range g = Set.range h ∪ Set.range e) :
    Set.range (f ≫ t) ∪ Set.range (g ≫ t) =
      Set.range (h ≫ t) ∪ Set.range (e ≫ t) := by
  change Set.range (t ∘ f) ∪ Set.range (t ∘ g) =
    Set.range (t ∘ h) ∪ Set.range (t ∘ e)
  simp only [Set.range_comp, ← Set.image_union, he]

/-- Exact pair coverage transports through specified equalities of whole scheme maps. -/
theorem componentRange_pair_eq_transport {A B C E X Y : Scheme.{u}}
    (f : A ⟶ X) (g : B ⟶ X) (h : C ⟶ X) (e : E ⟶ X) (t : X ⟶ Y)
    (f' : A ⟶ Y) (g' : B ⟶ Y) (h' : C ⟶ Y) (e' : E ⟶ Y)
    (hf : f ≫ t = f') (hg : g ≫ t = g') (hh : h ≫ t = h') (he : e ≫ t = e')
    (H : Set.range f ∪ Set.range g = Set.range h ∪ Set.range e) :
    Set.range f' ∪ Set.range g' = Set.range h' ∪ Set.range e' := by
  rw [← hf, ← hg, ← hh, ← he]
  exact componentRange_pair_eq_postcomp f g h e t H

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
local notation "K" => ResidueField R
/-- Rewriting the target stage preserves the original infinity chart map. -/
@[reassoc] theorem finiteInfinityTensorChart_index_transport {a b : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (he : a = b) :
    finiteInfinityTensorChart hπ data K a ha ≫
        eqToHom (finiteGlobalTensorModel_index_congr hπ data K ha hb he) =
      finiteInfinityTensorChart hπ data K b hb := by
  subst b
  simp only [eqToHom_refl, Category.comp_id]

/-- Exterior normalization preserves exactly the original complete exterior image. -/
theorem zeroRetainedOrientedToGlobal_range (j : ℕ) (hj : j + 1 ≤ n)
    (r : ℕ) (hr : j + 1 + r ≤ n) (hk0 : start + j = 0)
    (hdepth : 2 * (start + j + 1) ≤ depth) :
    Set.range (zeroRetainedOrientedToGlobal hπ data D j hj r hr hk0 hdepth) =
      Set.range (zeroRetainedExteriorToGlobal hπ data D j hj r hr hk0 hdepth) :=
  (zeroRetainedExteriorOrientedIso hπ data D j hj r hr hk0 hdepth).inv
    |>.homeomorph.surjective.range_comp
      (zeroRetainedExteriorToGlobal hπ data D j hj r hr hk0 hdepth)

/-- The actual exterior and first full conic cover the entire first chart and infinity. -/
theorem finalZeroExterior_conic_range :
    Set.range (finalZeroExteriorComponent hπ data D s hs hstart hk) ∪
        Set.range (retainedConicAt hπ data D (s + 1) hs 0 (by omega) (by omega)) =
      Set.range (retainedTensorChartAt hπ data (s + 1) hs 0 (by omega)) ∪
        Set.range (finiteInfinityTensorChart hπ data K (s + 1) hs) := by
  let t := componentCoverageTransport (finiteGlobalTensorModel_index_congr hπ data K
    (a := 0 + 1 + s) (b := s + 1) (by omega) hs (by omega))
  have H := zeroRetainedExterior_conic_cover hπ data D 0 (by omega) s (by omega)
    (by omega) (by omega)
  rw [← zeroRetainedOrientedToGlobal_range,
    ← orderedRetainedConic_zero hπ data D 0 (by omega) s (by omega) (by omega) (by omega),
    ← retainedConicAt_original hπ data D 0 (by omega) s (by omega),
    ← retainedTensorChartAt_original hπ data 0 (by omega) s (by omega)] at H
  exact componentRange_pair_eq_transport
    (zeroRetainedOrientedToGlobal hπ data D 0 (by omega) s
      (by omega) (by omega) (by omega))
    (retainedConicAt hπ data D (0 + 1 + s) (by omega) 0 (by omega) (by omega))
    (retainedTensorChartAt hπ data (0 + 1 + s) (by omega) 0 (by omega))
    (finiteInfinityTensorChart hπ data K (0 + 1 + s) (by omega)) t
    (finalZeroExteriorComponent hπ data D s hs hstart hk)
    (retainedConicAt hπ data D (s + 1) hs 0 (by omega) (by omega))
    (retainedTensorChartAt hπ data (s + 1) hs 0 (by omega))
    (finiteInfinityTensorChart hπ data K (s + 1) hs)
    (by dsimp only [t]; rw [componentCoverageTransport_def]; rfl)
    (by dsimp only [t]; rw [componentCoverageTransport_def]
        exact retainedConicAt_index_transport hπ data D _ hs (by omega) _ _ _)
    (by dsimp only [t]; rw [componentCoverageTransport_def]
        exact retainedTensorChartAt_index_transport hπ data _ hs (by omega) _ _)
    (by dsimp only [t]; rw [componentCoverageTransport_def]
        exact finiteInfinityTensorChart_index_transport hπ data _ hs (by omega)) H

end FLT.Mazur.WeierstrassDividedDepth
