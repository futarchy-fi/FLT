/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianTripleOverlapCoordinates
public import FLT.Mazur.GrassmannianOverlapTransitionScheme

/-!
# The scheme cocycle on the actual triple intersection

The successive triple localization is the pullback of the next determinant open
along the first rational transition. Its restricted maps to both successive
overlap schemes and the composite overlap give equal third-chart morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R : Type u} [CommRing R] {ι κ ν : Type u}
  [Fintype ι] [Fintype κ] [Fintype ν] {d : ℕ}
  (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R)))
  (f : ((Fin d → R) × (ν → R)) ≃ₗ[R] ((Fin d → R) × (κ → R)))

/-- The actual successive triple-intersection scheme. -/
def tripleOverlapScheme : Scheme.{u} := Spec (.of (tripleOverlapRing e f))

/-- Its principal open inclusion into the first overlap. -/
def tripleOverlapFirstScheme : tripleOverlapScheme e f ⟶ ambientOverlapScheme e :=
  Spec.map (CommRingCat.ofHom (tripleOverlapFirstHom e f).toRingHom)

/-- Its restricted morphism into the next overlap. -/
def tripleOverlapNextScheme : tripleOverlapScheme e f ⟶ ambientOverlapScheme f :=
  Spec.map (CommRingCat.ofHom (tripleOverlapNextHom e f).toRingHom)

/-- Its restricted morphism into the composite overlap. -/
def tripleOverlapCompositeScheme :
    tripleOverlapScheme e f ⟶ ambientOverlapScheme (f.trans e) :=
  Spec.map (CommRingCat.ofHom (tripleOverlapCompositeHom e f).toRingHom)

instance : IsOpenImmersion (tripleOverlapFirstScheme e f) :=
  inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap (ambientOverlapRing e) (tripleOverlapRing e f)))))

omit [Fintype ν] in
/-- Its open image is exactly the next determinant's basic open in the first overlap. -/
theorem tripleOverlapFirstScheme_range :
    (tripleOverlapFirstScheme e f).opensRange =
      PrimeSpectrum.basicOpen (tripleOverlapElement e f) :=
  Scheme.Hom.opensRange_localizationAway
    (R := CommRingCat.of (ambientOverlapRing e)) (tripleOverlapElement e f)

omit [Fintype ν] in
/-- The restricted map to the next overlap agrees with the first transition into its chart. -/
theorem tripleOverlapScheme_square :
    tripleOverlapFirstScheme e f ≫
      localizedChartTransitionScheme (ambientBlockP e.toLinearMap) (ambientBlockQ e.toLinearMap)
        (ambientBlockU e.toLinearMap) (ambientBlockT e.toLinearMap) =
      tripleOverlapNextScheme e f ≫
        principalOverlapInclusion (ambientBlockP f.toLinearMap) (ambientBlockQ f.toLinearMap) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact (tripleOverlapNextHom_algebraMap e f x).symm

omit [Fintype ν] in
/-- The constructed domain is the actual scheme pullback of the next overlap open. -/
theorem tripleOverlapScheme_isPullback :
    IsPullback (tripleOverlapNextScheme e f) (tripleOverlapFirstScheme e f)
      (principalOverlapInclusion (ambientBlockP f.toLinearMap) (ambientBlockQ f.toLinearMap))
      (localizedChartTransitionScheme (ambientBlockP e.toLinearMap) (ambientBlockQ e.toLinearMap)
        (ambientBlockU e.toLinearMap) (ambientBlockT e.toLinearMap)) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (tripleOverlapScheme_square e f)
  rw [principalOverlapInclusion_range, tripleOverlapFirstScheme_range]
  exact SpecMap_preimage_basicOpen
    (CommRingCat.ofHom (ambientTransitionPolynomialHom e).toRingHom) _

/-- The third-chart scheme cocycle holds on the actual triple-intersection pullback. -/
theorem tripleOverlapScheme_cocycle :
    tripleOverlapCompositeScheme e f ≫
      localizedChartTransitionScheme (ambientBlockP (f.trans e).toLinearMap)
        (ambientBlockQ (f.trans e).toLinearMap) (ambientBlockU (f.trans e).toLinearMap)
        (ambientBlockT (f.trans e).toLinearMap) =
      tripleOverlapNextScheme e f ≫
        localizedChartTransitionScheme (ambientBlockP f.toLinearMap)
          (ambientBlockQ f.toLinearMap) (ambientBlockU f.toLinearMap)
          (ambientBlockT f.toLinearMap) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (tripleOverlapPolynomial_cocycle e f)

/-- The original-chart embeddings of the composite and first overlaps agree on this domain. -/
theorem tripleOverlapScheme_original :
    tripleOverlapCompositeScheme e f ≫
      principalOverlapInclusion (ambientBlockP (f.trans e).toLinearMap)
        (ambientBlockQ (f.trans e).toLinearMap) =
      tripleOverlapFirstScheme e f ≫
        principalOverlapInclusion (ambientBlockP e.toLinearMap) (ambientBlockQ e.toLinearMap) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact tripleOverlapCompositeHom_algebraMap e f

end FLT.Mazur.GrassmannianChart
