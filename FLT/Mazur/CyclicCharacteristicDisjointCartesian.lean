/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointQuotient

/-!
# Cartesian components and finiteness of the assembled quotient

Pulling back either original characteristic component of the quotient recovers
exactly its original normalized source. Finiteness and properness therefore
hold for the single quotient map, not only for its separate component maps.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The inverse image of a quotient component is exactly its original source component. -/
theorem normalizedDisjointQuotientMap_preimage (b : Bool) :
    normalizedDisjointQuotientMap n ⁻¹ᵁ (normalizedDisjointQuotientInclusion n b).opensRange =
      (normalizedDisjointInclusion n b).opensRange := by
  apply le_antisymm
  · rintro x ⟨y, hxy⟩
    obtain ⟨c, z, rfl⟩ := (sigmaOpenCover (normalizedLocus n)).exists_eq x
    change normalizedDisjointQuotientInclusion n b y =
      (normalizedDisjointInclusion n c ≫ normalizedDisjointQuotientMap n) z at hxy
    rw [normalizedDisjointInclusion_quotientMap, Scheme.Hom.comp_apply] at hxy
    have hbc : b = c := congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp hxy)
    subst c
    exact ⟨z, rfl⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨normalizedQuotientMap n b x, ?_⟩
    exact (congrArg (fun f ↦ f x) (normalizedDisjointInclusion_quotientMap n b)).symm

/-- Both characteristic component squares are actual scheme pullbacks. -/
theorem normalizedDisjointQuotientMap_isPullback (b : Bool) :
    IsPullback (normalizedDisjointInclusion n b) (normalizedQuotientMap n b)
      (normalizedDisjointQuotientMap n) (normalizedDisjointQuotientInclusion n b) :=
  (IsOpenImmersion.isPullback _ _ _ _ (normalizedDisjointInclusion_quotientMap n b)
    (normalizedDisjointQuotientMap_preimage n b)).flip

/-- Finiteness of the actual component maps proves finiteness of the assembled quotient. -/
instance normalizedDisjointQuotientMap_finite : IsFinite (normalizedDisjointQuotientMap n) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsFinite)
    (sigmaOpenCover (normalizedQuotient n))
  intro b
  change IsFinite
    (pullback.snd (normalizedDisjointQuotientMap n) (normalizedDisjointQuotientInclusion n b))
  rw [← (normalizedDisjointQuotientMap_isPullback n b).isoPullback_inv_snd]
  infer_instance

/-- The single quotient map is proper. -/
instance normalizedDisjointQuotientMap_proper : IsProper (normalizedDisjointQuotientMap n) :=
  inferInstance

/-- The assembled quotient carries the actual quotient topology of the single source. -/
theorem normalizedDisjointQuotientMap_isQuotientMap :
    Topology.IsQuotientMap (normalizedDisjointQuotientMap n) :=
  (normalizedDisjointQuotientMap n).isClosedMap.isQuotientMap
    (normalizedDisjointQuotientMap n).continuous (normalizedDisjointQuotientMap n).surjective

/-- Fibers of the single quotient are exactly the orbits of its actual assembled action. -/
theorem normalizedDisjointQuotientMap_eq_iff_orbit (x y : normalizedDisjointSource n) :
    normalizedDisjointQuotientMap n x = normalizedDisjointQuotientMap n y ↔
      ∃ g : RelabelGroup n, y = (normalizedDisjointAction n g).hom x := by
  constructor
  · intro h
    obtain ⟨b, x, rfl⟩ := (sigmaOpenCover (normalizedLocus n)).exists_eq x
    obtain ⟨c, y, rfl⟩ := (sigmaOpenCover (normalizedLocus n)).exists_eq y
    have he : normalizedDisjointQuotientInclusion n b (normalizedQuotientMap n b x) =
        normalizedDisjointQuotientInclusion n c (normalizedQuotientMap n c y) := by
      change (normalizedDisjointInclusion n b ≫ normalizedDisjointQuotientMap n) x =
        (normalizedDisjointInclusion n c ≫ normalizedDisjointQuotientMap n) y at h
      simpa only [normalizedDisjointInclusion_quotientMap, Scheme.Hom.comp_apply] using h
    have hbc : b = c := congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp he)
    subst c
    have hq := (normalizedDisjointQuotientInclusion n b).isOpenEmbedding.injective he
    obtain ⟨g, rfl⟩ := (normalizedQuotientMap_eq_iff_orbit n b x y).mp hq
    refine ⟨g, ?_⟩
    exact (congrArg (fun f ↦ f x) (normalizedDisjointAction_inclusion n b g)).symm
  · rintro ⟨g, rfl⟩
    exact (congrArg (fun f ↦ f x) (normalizedDisjointQuotientMap_invariant n g)).symm

end FLT.Mazur.CyclicCharacteristicAtlas
