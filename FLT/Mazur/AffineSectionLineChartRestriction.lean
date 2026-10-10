/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSectionLineCanonicalRestriction
public import FLT.Mazur.FiniteFreeChartRestriction
public import FLT.Mazur.CoherentSubmoduleUnion
public import FLT.Mazur.FiniteFreeChartSectionLinePullback

/-!
# Section-line restriction inside the original ambient module

The canonical line comparison preserves the ambient inclusion on every
smaller affine open. This connects actual geometric restriction to the
slice subobjects used in the gluing construction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FiniteFreeChartTransitions
open AffineFreeSheafCoordinates NormalizedSectionLine OpenModuleRestrictionCoherence
open ModuleGlobalEvaluationPullback CoherentSubmoduleUnion
open ModuleSheafMorphismGluing
open FCurve.CoherentDevissage.ClosedDescentCharts
variable {X : Scheme.{u}} (M : X.Modules)

/-- The slice-gluing comparison is the inverse of the original nested restriction. -/
lemma nestedRestriction_eq_nested_inv {U V : X.Opens} (h : V ≤ U) :
    (nestedRestriction h).hom.app M = (nested M h).inv := by
  apply Scheme.Modules.hom_ext
  intro T
  simp only [nestedRestriction_hom_app, nested, Iso.trans_inv, Iso.app_inv,
    Scheme.Modules.Hom.comp_app, restrictFunctorComp_inv_app_app,
    restrictFunctorCongr_inv_app_app, ← Functor.map_comp]
  congr 1

variable {U V W : X.Opens} [IsAffine V.toScheme] [IsAffine W.toScheme]
variable (h : V ≤ U) (k : W ≤ V) {ι : Type u} [Finite ι]
variable (e : M.restrict U.ι ≅ SheafOfModules.free ι)

/-- The actual line restriction square commutes in the original ambient module. -/
lemma canonicalSectionLineRestriction_chart (i : ι) (L : Chart Γ(V.toScheme, ⊤) ι i) :
    (canonicalSectionLineRestriction (X.homOfLE k) i L).hom ≫
        chartSectionLineInclusion M (k.trans h) e i
          (baseChange (X.homOfLE k).appTop.hom i L) =
      CoherentSubmoduleUnion.mapOn M k (chartSectionLineInclusion M h e i L) := by
  dsimp only [chartSectionLineInclusion, CoherentSubmoduleUnion.mapOn]
  rw [refineChart_comp M h k, nestedRestriction_eq_nested_inv]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  rw [← Category.assoc (canonicalSectionLineRestriction (X.homOfLE k) i L).hom,
    canonicalSectionLineRestriction_inclusion]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The slice inclusion used for gluing recovers the actual extended chart line. -/
lemma sectionLine_slice_subobject (i : ι) (L : Chart Γ(V.toScheme, ⊤) ι i) :
    Subobject.mk (restrictionEquiv W
      (CoherentSubmoduleGluing.inclusionOn M (chartSectionLineInclusion M h e i L) k)) =
      Subobject.mk (chartSectionLineInclusion M (k.trans h) e i
        (baseChange (X.homOfLE k).appTop.hom i L)) := by
  rw [subobject_inclusionOn]
  exact Subobject.mk_eq_mk_of_comm _ _ (canonicalSectionLineRestriction (X.homOfLE k) i L)
    (canonicalSectionLineRestriction_chart M h k e i L)

end FLT.Mazur.FiniteFreeChartTransitions
