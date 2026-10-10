/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBoundarySeriesDegree
public import FLT.Mazur.PolygonInfinitesimalStageProper
public import FLT.Mazur.ProperRingCohomologyFinite

/-!
# Finite homogeneous sections on the original polygon stages

Each actual stage is proper over the power-series spectrum through its
closed coefficient immersion. Proper coherent cohomology gives finite
sections with exactly the original power-series scalar action.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback SectionGradedSum Chow.AffineBase

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family boundarySeriesScalars

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (m d : ℕ)

/-- Structural power-series coefficients agree with the proper composite structure map. -/
theorem boundarySeriesScalarMap_eq : boundarySeriesScalarMap K n h m =
    baseCohomologyScalars ((family K m n h).hom ≫ baseToSeries K m) := by
  ext r
  change (family K m n h).hom.appTop
    ((Scheme.ΓSpecIso (.of (Ring K m))).inv (seriesToStage K m r)) =
      ((family K m n h).hom ≫ baseToSeries K m).appTop
        ((Scheme.ΓSpecIso (.of (PowerSeries K))).inv r)
  rw [Scheme.Hom.comp_appTop]
  apply congrArg (family K m n h).hom.appTop
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (seriesToStage K m).toRingHom)) r

/-- Insert actual zero-cohomology classes into their original homogeneous stage module. -/
def boundaryCohomologyToDegree :
    ModuleRingH (boundarySeriesScalarMap K n h m)
      (tensorPower (boundaryLine K m n h) d) 0 →ₗ[PowerSeries K]
        boundarySeriesDegree K n h m d where
  toFun x := ⟨of (boundaryLine K m n h) ⊤ d (moduleH0Equiv _ x), ⟨_, rfl⟩⟩
  map_add' x y := Subtype.ext (by simp only [map_add]; rfl)
  map_smul' r x := by
    apply Subtype.ext
    change of (boundaryLine K m n h) ⊤ d
      (moduleH0Equiv _ (boundarySeriesScalarMap K n h m r •
        (show ModuleH (tensorPower (boundaryLine K m n h) d) 0 from x))) = _
    rw [map_smul, map_smul, Algebra.smul_def, boundarySeriesScalarMap_algebraMap]
    exact (boundarySeriesDegree_smul_val K n h m d r
      ⟨of (boundaryLine K m n h) ⊤ d (moduleH0Equiv _ x), ⟨_, rfl⟩⟩).symm

/-- Homogeneous insertion reaches every original stage section in the specified degree. -/
theorem boundaryCohomologyToDegree_surjective :
    Function.Surjective (boundaryCohomologyToDegree K n h m d) := by
  rintro ⟨s, ⟨u, rfl⟩⟩
  obtain ⟨x, hx⟩ := (moduleH0Equiv (tensorPower (boundaryLine K m n h) d)).surjective u
  exact ⟨x, Subtype.ext (congrArg (of (boundaryLine K m n h) ⊤ d) hx)⟩

/-- Every original homogeneous stage module is finite over its actual complete coefficient base. -/
theorem boundarySeriesDegree_finite : Module.Finite (PowerSeries K)
    (boundarySeriesDegree K n h m d) := by
  let _ := ((boundaryLine_rankOne K m n h).tensorPower d).isFinitePresentation
  have hf := proper_coherent_hasFiniteRingCohomology
    ((family K m n h).hom ≫ baseToSeries K m) (tensorPower (boundaryLine K m n h) d) 0
  rw [← boundarySeriesScalarMap_eq] at hf
  let _ := hf
  exact Module.Finite.of_surjective (boundaryCohomologyToDegree K n h m d)
    (boundaryCohomologyToDegree_surjective K n h m d)

end FLT.Mazur.PolygonInfinitesimalStages
