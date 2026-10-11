/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseOpenHilbertOrbitHomeomorph

/-!
# Original source-section domains on every base-local quotient subopen

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
  (d : ℕ) (T₀ : Over (Spec (.of R))) [IsOpenImmersion T₀.hom]
  (c : (relativeFppfSheaf f).obj.obj (op T₀))

/-- All opens of the parameter scheme, regarded as actual opens of the original orbit. -/
def baseOpenChartOrbitOpens :
    TopologicalSpace.Opens (variableHilbertTest f d T₀).left ⥤
      Opens (Orbit (smoothHilbertEquivalenceRelation f hL)) :=
  Opens.map (TopCat.ofHom (baseOpenOrbitToChart f hL d T₀ c)) ⋙
    (Opens.isOpenEmbedding (X := space (smoothHilbertEquivalenceRelation f hL))
      (baseOpenOrbitOpen f hL d T₀ c)).functor

/-- The original quotient preimage of each chart subopen is the source immersion image. -/
theorem baseOpenChartOrbitOpen_preimage (W : (variableHilbertTest f d T₀).left.Opens) :
    (pullOpen (smoothHilbertEquivalenceRelation f hL)
      ((baseOpenChartOrbitOpens f hL d T₀ c).obj W)).val =
    (variableSourceInclusion f hL d T₀ c).left ''ᵁ
      ((variableSourceParameter f hL d T₀ c).left ⁻¹ᵁ W) := by
  ext x
  constructor
  · rintro ⟨z, hz, he⟩
    obtain ⟨y, hy⟩ := baseOpenSourceOrbitMap_surjective f hL d T₀ c z
    have hxy : projection (smoothHilbertEquivalenceRelation f hL)
        ((variableSourceInclusion f hL d T₀ c).left y) =
        projection (smoothHilbertEquivalenceRelation f hL) x :=
      (congrArg Subtype.val hy).trans he
    have hx : x ∈ baseOpenSourceOpen f hL d T₀ c := by
      apply (mem_baseOpenOrbitOpen_iff f hL d T₀ c x).mp
      exact he ▸ z.property
    obtain ⟨y', rfl⟩ := hx
    refine ⟨y', ?_, rfl⟩
    have hparam := (baseOpenSource_related_iff f hL d T₀ c y y').mp
      ((projection_eq_iff (smoothHilbertEquivalenceRelation f hL) _ _).mp hxy)
    change (variableSourceParameter f hL d T₀ c).left y' ∈ W
    rw [← hparam, ← baseOpenOrbitToChart_source, hy]
    exact hz
  · rintro ⟨y, hy, rfl⟩
    refine ⟨baseOpenSourceOrbitMap f hL d T₀ c y, ?_, rfl⟩
    change baseOpenOrbitToChart f hL d T₀ c (baseOpenSourceOrbitMap f hL d T₀ c y) ∈ W
    rwa [baseOpenOrbitToChart_source]

/-- Original source functions and source-chart functions have identical open domains. -/
def baseOpenChartSourceSectionsIso (W : (variableHilbertTest f d T₀).left.Opens) :
    (sourceSheaf (smoothHilbertEquivalenceRelation f hL)).obj.obj
      (op ((baseOpenChartOrbitOpens f hL d T₀ c).obj W)) ≅
    Γ((variableSourceIntersection f hL d T₀ c).left,
      (variableSourceParameter f hL d T₀ c).left ⁻¹ᵁ W) :=
  (smoothHilbertSource f).left.presheaf.mapIso
    (eqToIso (congrArg op (baseOpenChartOrbitOpen_preimage f hL d T₀ c W))) ≪≫
      (variableSourceInclusion f hL d T₀ c).left.appIso _

/-- The source-open identification respects inclusion of every chart subopen. -/
def baseOpenChartSourceOpenIso :
    baseOpenChartOrbitOpens f hL d T₀ c ⋙
      Opens.map (quotientMap (smoothHilbertEquivalenceRelation f hL)) ≅
    Opens.map (variableSourceParameter f hL d T₀ c).left.base ⋙
      (variableSourceInclusion f hL d T₀ c).left.opensFunctor :=
  NatIso.ofComponents (fun W ↦ eqToIso (baseOpenChartOrbitOpen_preimage f hL d T₀ c W))
    (by intros; apply Subsingleton.elim)

/-- The source immersion identifies structure presheaves on all parameter inverse images. -/
def baseOpenChartImmersionSectionsIso :
    (Opens.map (variableSourceParameter f hL d T₀ c).left.base ⋙
      (variableSourceInclusion f hL d T₀ c).left.opensFunctor).op ⋙
        (smoothHilbertSource f).left.presheaf ≅
    (Opens.map (variableSourceParameter f hL d T₀ c).left.base).op ⋙
      (variableSourceIntersection f hL d T₀ c).left.presheaf :=
  NatIso.ofComponents (fun W ↦ (variableSourceInclusion f hL d T₀ c).left.appIso
    ((variableSourceParameter f hL d T₀ c).left ⁻¹ᵁ W.unop)) (by
      intro W V k
      exact (variableSourceInclusion f hL d T₀ c).left.appIso_hom_naturality
        ((Opens.map (variableSourceParameter f hL d T₀ c).left.base).map k.unop).op)

/-- The original source-section comparison is natural for every restriction map. -/
def baseOpenChartSourcePresheafIso :
    (baseOpenChartOrbitOpens f hL d T₀ c).op ⋙
      (sourceSheaf (smoothHilbertEquivalenceRelation f hL)).obj ≅
    (Opens.map (variableSourceParameter f hL d T₀ c).left.base).op ⋙
      (variableSourceIntersection f hL d T₀ c).left.presheaf :=
  Functor.isoWhiskerRight (NatIso.op (baseOpenChartSourceOpenIso f hL d T₀ c).symm)
    (smoothHilbertSource f).left.presheaf ≪≫ baseOpenChartImmersionSectionsIso f hL d T₀ c

/-- The natural comparison has exactly the previously constructed open-ring components. -/
theorem baseOpenChartSourcePresheafIso_app (W : (variableHilbertTest f d T₀).left.Opens) :
    (baseOpenChartSourcePresheafIso f hL d T₀ c).app (op W) =
      baseOpenChartSourceSectionsIso f hL d T₀ c W := by
  ext : 1
  simp [baseOpenChartSourcePresheafIso, baseOpenChartSourceOpenIso,
    baseOpenChartImmersionSectionsIso, baseOpenChartSourceSectionsIso]

end FLT.Mazur.HilbertChart
