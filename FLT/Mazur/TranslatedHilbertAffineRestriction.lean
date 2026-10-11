/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallyRingedOpenImage
public import FLT.Mazur.TranslatedHilbertAffineImmersion

/-!
# Actual affine restrictions of the invariant quotient

Restricting the original quotient to a transported affine parameter open gives
that actual affine scheme as a locally ringed space. These opens cover each
translated chart and refine every neighborhood within the chart.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (i : TranslatedHilbertIndex f)

/-- Restriction to the transported parameter open is the original open subscheme. -/
def translatedParameterOpenLocallyRingedIso (W : (acyclicHilbertTest f i.1).left.Opens) :
    invariantOpenSpace (smoothHilbertEquivalenceRelation f hL)
      ((translatedChartOrbitOpens f hL i).obj W) ≅ W.toScheme.toLocallyRingedSpace :=
  LocallyRingedOpenImage.restrictIso (translatedParameterOpenImmersion f hL i W)
    ((translatedChartOrbitOpens f hL i).obj W)
    (translatedParameterOpenImmersion_range f hL i W)

/-- An affine parameter open makes the actual quotient restriction affine. -/
def translatedAffineOrbitOpenIso (W : (acyclicHilbertTest f i.1).left.Opens)
    (hW : IsAffineOpen W) :
    invariantOpenSpace (smoothHilbertEquivalenceRelation f hL)
      ((translatedChartOrbitOpens f hL i).obj W) ≅ (Spec Γ(_, W)).toLocallyRingedSpace :=
  translatedParameterOpenLocallyRingedIso f hL i W ≪≫
    Scheme.forgetToLocallyRingedSpace.mapIso hW.isoSpec

/-- Affine refinements stay inside their original translated chart. -/
theorem translatedChartOrbitOpens_le (W : (acyclicHilbertTest f i.1).left.Opens) :
    (translatedChartOrbitOpens f hL i).obj W ≤ translatedOrbitOpen f hL i := by
  rintro z ⟨x, _, rfl⟩
  exact x.property

/-- The affine refinements cover every point of the actual translated quotient chart. -/
theorem translatedAffineOrbitOpen_covers (z : translatedOrbitOpen f hL i) :
    ∃ W : (acyclicHilbertTest f i.1).left.Opens, IsAffineOpen W ∧
      z.val ∈ (translatedChartOrbitOpens f hL i).obj W := by
  obtain ⟨W, hW, hz⟩ := translatedOrbitOpen_exists_affine f hL i z
  refine ⟨W, hW, ?_⟩
  exact Set.ext_iff.mp (translatedParameterOpenImmersion_range f hL i W) z.val |>.mp hz

/-- Affine quotient charts refine every original orbit neighborhood inside this chart. -/
theorem translatedAffineOrbitOpen_refines
    (V : Opens (Orbit (smoothHilbertEquivalenceRelation f hL)))
    (z : translatedOrbitOpen f hL i) (hz : z.val ∈ V) :
    ∃ W : (acyclicHilbertTest f i.1).left.Opens, IsAffineOpen W ∧
      z.val ∈ (translatedChartOrbitOpens f hL i).obj W ∧
        (translatedChartOrbitOpens f hL i).obj W ≤ V := by
  let k := (translatedParameterOpenImmersion f hL i ⊤).base
  let x : (⊤ : (acyclicHilbertTest f i.1).left.Opens) :=
    ⟨translatedOrbitToChart f hL i z, trivial⟩
  have hk : k x = z.val :=
    congrArg Subtype.val ((translatedOrbitChartHomeomorph f hL i).symm_apply_apply z)
  let j := (translatedOrbitChartLocallyRingedIso f hL i).inv.base ≫
    (Opens.inclusion' (X := space (smoothHilbertEquivalenceRelation f hL))
      (translatedOrbitOpen f hL i))
  have hx : translatedOrbitToChart f hL i z ∈ (Opens.map j).obj V := by
    change k x ∈ V
    rwa [hk]
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hx
  refine ⟨W, hW, ?_, ?_⟩
  · exact ⟨z, hxW, rfl⟩
  · rintro y ⟨t, ht, rfl⟩
    have hv := hWV ht
    change (translatedChartToOrbit f hL i (translatedOrbitToChart f hL i t)).val ∈ V at hv
    have he : (translatedChartToOrbit f hL i
        (translatedOrbitToChart f hL i t)).val = t.val :=
      congrArg Subtype.val ((translatedOrbitChartHomeomorph f hL i).symm_apply_apply t)
    rw [he] at hv
    exact hv

end FLT.Mazur.HilbertChart
