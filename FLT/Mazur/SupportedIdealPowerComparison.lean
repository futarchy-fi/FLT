/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenImmersionIdealCorrespondence
public import FLT.Mazur.SectionDivisors
public import FLT.Mazur.PolygonDivisorPowerPullback

/-!
# Detecting full divisor powers on a support-containing open

Equality on an open containing both closed supports detects equality of the
whole ideal sheaves. In particular an orbit power computed on a torus extends
to the full curve, without discarding any nilpotent structure.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.OpenIdealCover

universe u
variable {X Y Z : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]

/-- Full supported ideals are determined by their restrictions to the containing open. -/
theorem eq_of_supported_comap_eq (I J : Y.IdealSheafData)
    (hI : Set.range I.subschemeι ⊆ Set.range j)
    (hJ : Set.range J.subschemeι ⊆ Set.range j)
    (h : I.comap j = J.comap j) : I = J := by
  rw [← open_map_comap j I hI, ← open_map_comap j J hJ, h]

/-- Restriction recovers the full kernel of a closed map into the open. -/
theorem ker_comp_comap (i : Z ⟶ X) [IsClosedImmersion (i ≫ j)] :
    (i ≫ j).ker.comap j = i.ker := by
  let hpb : IsPullback i (𝟙 _) j (i ≫ j) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso hpb.isoPullback.hom, hpb.isoPullback_hom_fst]

omit [IsOpenImmersion j] in
/-- A positive power of the kernel of a closed map from the open is still supported there. -/
theorem ker_comp_power_support (i : Z ⟶ X) [IsClosedImmersion (i ≫ j)]
    (n : ℕ) (hn : n ≠ 0) :
    Set.range ((i ≫ j).ker ^ n).subschemeι ⊆ Set.range j := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_pow _ _ hn,
    Scheme.Hom.support_ker, (i ≫ j).isClosedEmbedding.isClosed_range.closure_eq]
  rintro _ ⟨z, rfl⟩
  exact ⟨i z, rfl⟩

/-- A supported ideal whose open restriction is a kernel power is that power globally. -/
theorem eq_ker_comp_power (I : Y.IdealSheafData)
    (hI : Set.range I.subschemeι ⊆ Set.range j)
    (i : Z ⟶ X) [IsClosedImmersion (i ≫ j)] (n : ℕ) (hn : n ≠ 0)
    (h : I.comap j = i.ker ^ n) : I = (i ≫ j).ker ^ n := by
  apply eq_of_supported_comap_eq j I _ hI (ker_comp_power_support j i n hn)
  rw [FCurve.idealSheaf_comap_pow, ker_comp_comap, h]

end FLT.Mazur.OpenIdealCover
