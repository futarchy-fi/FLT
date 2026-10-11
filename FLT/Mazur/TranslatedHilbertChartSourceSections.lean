/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertOrbitHomeomorph

/-!
# Original source-section domains on every translated quotient subopen

The actual orbit chart homeomorphism and the open source immersion identify
all relevant section domains. The comparison uses the immersion's appIso,
so no new structure sheaf or replacement source is introduced.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (i : TranslatedHilbertIndex f)

/-- All opens of the parameter scheme, regarded as actual opens of the original orbit. -/
def translatedChartOrbitOpens :
    TopologicalSpace.Opens (acyclicHilbertTest f i.1).left ⥤
      Opens (Orbit (smoothHilbertEquivalenceRelation f hL)) :=
  Opens.map (TopCat.ofHom (translatedOrbitToChart f hL i)) ⋙
    (Opens.isOpenEmbedding (X := space (smoothHilbertEquivalenceRelation f hL))
      (translatedOrbitOpen f hL i)).functor

/-- The original quotient preimage of each chart subopen is the source immersion image. -/
theorem translatedChartOrbitOpen_preimage (W : (acyclicHilbertTest f i.1).left.Opens) :
    (pullOpen (smoothHilbertEquivalenceRelation f hL)
      ((translatedChartOrbitOpens f hL i).obj W)).val =
    (translatedSourceInclusion f hL i).left ''ᵁ
      ((translatedSourceParameter f hL i).left ⁻¹ᵁ W) := by
  ext x
  constructor
  · rintro ⟨z, hz, he⟩
    obtain ⟨y, hy⟩ := translatedSourceOrbitMap_surjective f hL i z
    have hxy : projection (smoothHilbertEquivalenceRelation f hL)
        ((translatedSourceInclusion f hL i).left y) =
        projection (smoothHilbertEquivalenceRelation f hL) x :=
      (congrArg Subtype.val hy).trans he
    have hx : x ∈ translatedSourceOpen f hL i := by
      apply (mem_translatedOrbitOpen_iff f hL i x).mp
      exact he ▸ z.property
    obtain ⟨y', rfl⟩ := hx
    refine ⟨y', ?_, rfl⟩
    have hparam := (translatedSource_related_iff f hL i y y').mp
      ((projection_eq_iff (smoothHilbertEquivalenceRelation f hL) _ _).mp hxy)
    change (translatedSourceParameter f hL i).left y' ∈ W
    rw [← hparam, ← translatedOrbitToChart_source, hy]
    exact hz
  · rintro ⟨y, hy, rfl⟩
    refine ⟨translatedSourceOrbitMap f hL i y, ?_, rfl⟩
    change translatedOrbitToChart f hL i (translatedSourceOrbitMap f hL i y) ∈ W
    rwa [translatedOrbitToChart_source]

/-- Original source functions and source-chart functions have identical open domains. -/
def translatedChartSourceSectionsIso (W : (acyclicHilbertTest f i.1).left.Opens) :
    (sourceSheaf (smoothHilbertEquivalenceRelation f hL)).obj.obj
      (op ((translatedChartOrbitOpens f hL i).obj W)) ≅
    Γ((translatedSourceIntersection f hL i).left,
      (translatedSourceParameter f hL i).left ⁻¹ᵁ W) :=
  (smoothHilbertSource f).left.presheaf.mapIso
    (eqToIso (congrArg op (translatedChartOrbitOpen_preimage f hL i W))) ≪≫
      (translatedSourceInclusion f hL i).left.appIso _

/-- The source-open identification respects inclusion of every chart subopen. -/
def translatedChartSourceOpenIso :
    translatedChartOrbitOpens f hL i ⋙
      Opens.map (quotientMap (smoothHilbertEquivalenceRelation f hL)) ≅
    Opens.map (translatedSourceParameter f hL i).left.base ⋙
      (translatedSourceInclusion f hL i).left.opensFunctor :=
  NatIso.ofComponents (fun W ↦ eqToIso (translatedChartOrbitOpen_preimage f hL i W))
    (by intros; apply Subsingleton.elim)

/-- The source immersion identifies structure presheaves on all parameter inverse images. -/
def translatedChartImmersionSectionsIso :
    (Opens.map (translatedSourceParameter f hL i).left.base ⋙
      (translatedSourceInclusion f hL i).left.opensFunctor).op ⋙
        (smoothHilbertSource f).left.presheaf ≅
    (Opens.map (translatedSourceParameter f hL i).left.base).op ⋙
      (translatedSourceIntersection f hL i).left.presheaf :=
  NatIso.ofComponents (fun W ↦ (translatedSourceInclusion f hL i).left.appIso
    ((translatedSourceParameter f hL i).left ⁻¹ᵁ W.unop)) (by
      intro W V k
      exact (translatedSourceInclusion f hL i).left.appIso_hom_naturality
        ((Opens.map (translatedSourceParameter f hL i).left.base).map k.unop).op)

/-- The original source-section comparison is natural for every restriction map. -/
def translatedChartSourcePresheafIso :
    (translatedChartOrbitOpens f hL i).op ⋙
      (sourceSheaf (smoothHilbertEquivalenceRelation f hL)).obj ≅
    (Opens.map (translatedSourceParameter f hL i).left.base).op ⋙
      (translatedSourceIntersection f hL i).left.presheaf :=
  Functor.isoWhiskerRight (NatIso.op (translatedChartSourceOpenIso f hL i).symm)
    (smoothHilbertSource f).left.presheaf ≪≫ translatedChartImmersionSectionsIso f hL i

/-- The natural comparison has exactly the previously constructed open-ring components. -/
theorem translatedChartSourcePresheafIso_app (W : (acyclicHilbertTest f i.1).left.Opens) :
    (translatedChartSourcePresheafIso f hL i).app (op W) =
      translatedChartSourceSectionsIso f hL i W := by
  ext : 1
  simp [translatedChartSourcePresheafIso, translatedChartSourceOpenIso,
    translatedChartImmersionSectionsIso, translatedChartSourceSectionsIso]

end FLT.Mazur.HilbertChart
