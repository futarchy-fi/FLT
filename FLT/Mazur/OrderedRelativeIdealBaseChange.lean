/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedRelativeIdealFamily

/-!
# Arbitrary base change of full ordered ideal families

Fiber-product symmetry commutes with the actual ambient maps. The proved
base-change equality of graph ideals therefore gives equality of the full
ordered families and specialization of the universal ordered family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover Scheme.IdealSheafData

namespace FLT.Mazur.OrderedCurvePower

set_option backward.isDefEq.respectTransparency false

variable {Z S X Y : Scheme.{0}} (z : Z ⟶ S) (d : ℕ)
variable [SmoothOfRelativeDimension 1 z] [IsProper z]
variable (s : X ⟶ S) (t : Y ⟶ S) (g : Y ⟶ X) (hg : g ≫ s = t)
variable (x : Fin d → (X ⟶ Z)) (hx : ∀ i, x i ≫ z = s)

omit [SmoothOfRelativeDimension 1 z] [IsProper z] in
/-- Actual ambient base change commutes with the symmetry of the fiber product. -/
theorem relativeIdealAmbientMap_symmetry :
    relativeIdealAmbientMap z s t g hg ≫ (pullbackSymmetry s z).hom =
      (pullbackSymmetry t z).hom ≫ CurveGraphPullback.curveMap z s t g hg := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
      pullbackSymmetry_hom_comp_snd, relativeIdealAmbientMap_fst, relativeIdealAmbientMap_snd,
      CurveGraphPullback.curveMap_fst, CurveGraphPullback.curveMap_snd,
      pullbackSymmetry_hom_comp_snd_assoc]

/-- The full tuple family commutes with every test-scheme base change. -/
theorem tupleRelativeIdealFamily_baseChange :
    relativeIdealFamilyBaseChange z d s t g hg (tupleRelativeIdealFamily z d s x hx) =
      tupleRelativeIdealFamily z d t (fun i ↦ g ≫ x i)
        (fun i ↦ by rw [Category.assoc, hx i, hg]) := by
  apply Subtype.ext
  change ((tupleDivisorIdeal z d s x hx).comap _).comap _ = _
  rw [← comap_comp, relativeIdealAmbientMap_symmetry, comap_comp]
  congr 1
  simp only [tupleDivisorIdeal, FCurve.idealSheaf_comap_prod,
    CurveGraphPullback.graph_ker_comap]

/-- Pullback from the universal ordered space recovers the full family of any tuple. -/
theorem orderedRelativeIdealFamily_specialize :
    relativeIdealFamilyBaseChange z d (base z d) s (classify z d s x hx)
      (classify_base z d s x hx) (orderedRelativeIdealFamily z d) =
        tupleRelativeIdealFamily z d s x hx := by
  rw [orderedRelativeIdealFamily, tupleRelativeIdealFamily_baseChange]
  simp only [classify_point]

end FLT.Mazur.OrderedCurvePower
