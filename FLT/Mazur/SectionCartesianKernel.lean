/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeSums

/-!
# Section ideals in specified cartesian family squares

Compatible sections of a cartesian family square form a cartesian square of
closed immersions. Their actual kernel ideals, and finite sums of those ideals,
therefore agree under pullback along the specified family morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve

variable {X Y S T : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ T}
  {p : X ⟶ Y} {q : S ⟶ T}

/-- Compatible sections of a cartesian family square form a cartesian section square. -/
theorem section_isPullback_of_cartesian (H : IsPullback p f g q)
    (s : S ⟶ X) (t : T ⟶ Y) (hs : s ≫ f = 𝟙 _) (ht : t ≫ g = 𝟙 _)
    (hst : s ≫ p = q ≫ t) : IsPullback s q p t := by
  have K : IsPullback (s ≫ f) q q (t ≫ g) := by
    rw [hs, ht]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact K.of_right hst H.flip

/-- Pullback along the actual family map identifies the actual section kernels. -/
theorem section_ker_comap_of_cartesian (H : IsPullback p f g q) [IsSeparated g]
    (s : S ⟶ X) (t : T ⟶ Y) (hs : s ≫ f = 𝟙 _) (ht : t ≫ g = 𝟙 _)
    (hst : s ≫ p = q ≫ t) : t.ker.comap p = s.ker := by
  let _ := isClosedImmersion_section g t ht
  have K := section_isPullback_of_cartesian H s t hs ht hst
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso K.isoPullback.hom, K.isoPullback_hom_fst]

/-- The full sum of compatible section divisors retains its scheme-theoretic ideal. -/
theorem section_prod_comap_of_cartesian {ι : Type*} (H : IsPullback p f g q)
    [IsSeparated g] (indices : Finset ι) (s : ι → (S ⟶ X)) (t : ι → (T ⟶ Y))
    (hs : ∀ i, s i ≫ f = 𝟙 _) (ht : ∀ i, t i ≫ g = 𝟙 _)
    (hst : ∀ i, s i ≫ p = q ≫ t i) :
    (∏ i ∈ indices, (t i).ker).comap p = ∏ i ∈ indices, (s i).ker := by
  rw [idealSheaf_comap_prod]
  exact Finset.prod_congr rfl fun i _ ↦
    section_ker_comap_of_cartesian H (s i) (t i) (hs i) (ht i) (hst i)

end FLT.Mazur.FCurve
