/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianTripleOverlapDeterminant
public import FLT.Mazur.GrassmannianTripleOverlapScheme

/-!
# Triple overlaps as pullbacks over the original chart

The successive localization is also the intersection of the first and composite
principal opens of the original chart. This supplies the actual domain required
by the scheme gluing API, with its canonical pullback comparison isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R : Type u} [CommRing R] {ι κ ν : Type u}
  [Fintype ι] [Fintype κ] [Fintype ν] {d : ℕ}
  (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R)))
  (f : ((Fin d → R) × (ν → R)) ≃ₗ[R] ((Fin d → R) × (κ → R)))

/-- The triple domain is the actual intersection of the two original-chart principal opens. -/
theorem tripleOverlapScheme_original_isPullback :
    IsPullback (tripleOverlapCompositeScheme e f) (tripleOverlapFirstScheme e f)
      (principalOverlapInclusion (ambientBlockP (f.trans e).toLinearMap)
        (ambientBlockQ (f.trans e).toLinearMap))
      (principalOverlapInclusion (ambientBlockP e.toLinearMap) (ambientBlockQ e.toLinearMap)) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (tripleOverlapScheme_original e f).symm
  rw [principalOverlapInclusion_range, tripleOverlapFirstScheme_range]
  change (Spec.map (CommRingCat.ofHom (algebraMap _ (ambientOverlapRing e)))) ⁻¹ᵁ _ = _
  rw [SpecMap_preimage_basicOpen]
  exact tripleOverlap_compositeBasicOpen e f

/-- Canonical comparison from the actual triple localization to the gluing pullback. -/
def tripleOverlapOriginalPullbackIso :
    tripleOverlapScheme e f ≅
      pullback
        (principalOverlapInclusion (ambientBlockP e.toLinearMap) (ambientBlockQ e.toLinearMap))
        (principalOverlapInclusion (ambientBlockP (f.trans e).toLinearMap)
          (ambientBlockQ (f.trans e).toLinearMap)) :=
  (tripleOverlapScheme_original_isPullback e f).flip.isoPullback

/-- The comparison preserves the first overlap projection. -/
@[reassoc] theorem tripleOverlapOriginalPullbackIso_fst :
    (tripleOverlapOriginalPullbackIso e f).hom ≫ pullback.fst _ _ =
      tripleOverlapFirstScheme e f := by
  exact (tripleOverlapScheme_original_isPullback e f).flip.isoPullback_hom_fst

/-- The comparison preserves the composite overlap projection. -/
@[reassoc] theorem tripleOverlapOriginalPullbackIso_snd :
    (tripleOverlapOriginalPullbackIso e f).hom ≫ pullback.snd _ _ =
      tripleOverlapCompositeScheme e f := by
  exact (tripleOverlapScheme_original_isPullback e f).flip.isoPullback_hom_snd

end FLT.Mazur.GrassmannianChart
