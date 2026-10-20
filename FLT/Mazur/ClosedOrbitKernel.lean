/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeSums

/-!
# Full orbit ideals under closed embeddings

Restriction along a monomorphism retains each closed section kernel. If their
full product vanishes in the source, the ambient orbit divisor contains the
whole image scheme, with all multiplicities retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.ClosedOrbitKernel

universe u
variable {X Y Z : Scheme.{u}} (j : X ⟶ Y)

/-- A morphism's full image ideal pulls back to zero on its source. -/
theorem ker_comap_self : j.ker.comap j = ⊥ := by
  apply le_antisymm _ bot_le
  simpa only [Scheme.IdealSheafData.map_bot] using
    Scheme.IdealSheafData.comap_map_le (⊥ : X.IdealSheafData) j

/-- Pulling a closed composite back along a monomorphism recovers the full original kernel. -/
theorem ker_comp_comap [Mono j] (i : Z ⟶ X) [IsClosedImmersion (i ≫ j)] :
    (i ≫ j).ker.comap j = i.ker := by
  let hpb : IsPullback i (𝟙 _) j (i ≫ j) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso hpb.isoPullback.hom, hpb.isoPullback_hom_fst]

/-- Restriction preserves every factor of an ambient closed orbit product. -/
theorem orbit_comap [Mono j] {ι : Type*} (s : Finset ι) (i : ι → (Z ⟶ X))
    [∀ a, IsClosedImmersion (i a ≫ j)] :
    (∏ a ∈ s, (i a ≫ j).ker).comap j = ∏ a ∈ s, (i a).ker := by
  rw [FCurve.idealSheaf_comap_prod]
  simp only [ker_comp_comap]

/-- Intrinsic vanishing of the full orbit product puts the whole image inside the orbit divisor. -/
theorem orbit_le_ker [Mono j] {ι : Type*} (s : Finset ι) (i : ι → (Z ⟶ X))
    [∀ a, IsClosedImmersion (i a ≫ j)] (h : ∏ a ∈ s, (i a).ker = ⊥) :
    ∏ a ∈ s, (i a ≫ j).ker ≤ j.ker := by
  rw [← Scheme.IdealSheafData.map_bot j, Scheme.IdealSheafData.le_map_iff_comap_le,
    orbit_comap, h]

end FLT.Mazur.ClosedOrbitKernel
