/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalAtlas
public import FLT.Mazur.PolygonSmoothingFlat

/-!
# Flat arithmetic families from the infinitesimal cyclic atlas

The chart structure maps descend to the assembled scheme. Its finite affine
open cover proves flatness and local finite presentation over the original base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped LaurentPolynomial

universe u

namespace FLT.Mazur.PolygonInfinitesimal

set_option backward.isDefEq.respectTransparency false

open PolygonSmoothing

variable (R : Type u) [CommRing R] (t : R) (n : ℕ)

/-- The compatible original coefficient maps on the arithmetic cyclic diagram. -/
def baseCocone : Cocone (diagram R t n) where
  pt := Spec (.of R)
  ι.app j := match j with
    | .left _ => Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹]))
    | .right _ => chartStructure R t
  ι.naturality := by
    intro i j f
    cases f with
    | id i => simp
    | fst i => exact (leftBranchOpen_base R t).trans (Category.comp_id _).symm
    | snd i => exact (precedingBranch_base R t).trans (Category.comp_id _).symm

variable [Fact (IsNilpotent t)] (h : 2 ≤ n)

/-- The structure morphism of the actual glued arithmetic scheme. -/
def toBase : scheme R t n h ⟶ Spec (.of R) :=
  letI : Fact (2 ≤ n) := ⟨h⟩
  colimit.desc (diagram R t n) (baseCocone R t n)

/-- Every chart retains its original arithmetic structure morphism. -/
@[reassoc (attr := simp)] theorem chart_toBase (i : Fin n) :
    chart R t n h i ≫ toBase R t n h = chartStructure R t := by
  let : Fact (2 ≤ n) := ⟨h⟩
  exact colimit.ι_desc (baseCocone R t n) (.right i)

/-- The original smoothing charts form a finite affine open cover. -/
def chartCover : (scheme R t n h).OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (Fin n)
    (fun _ ↦ PolygonSmoothing.chart R t) (chart R t n h)
    (fun x ↦ by
      obtain ⟨i, y, hy⟩ := charts_cover R t n h x
      exact ⟨i, y, hy⟩) (fun _ ↦ inferInstance)

/-- The assembled infinitesimal polygon is flat over its actual coefficient base. -/
instance toBase_flat : Flat (toBase R t n h) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (chartCover R t n h)).mpr
  intro i
  change Flat (chart R t n h i ≫ toBase R t n h)
  rw [chart_toBase]
  infer_instance

/-- The assembled infinitesimal polygon is locally finitely presented over its base. -/
instance toBase_locallyOfFinitePresentation : LocallyOfFinitePresentation (toBase R t n h) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (chartCover R t n h)).mpr
  intro i
  change LocallyOfFinitePresentation (chart R t n h i ≫ toBase R t n h)
  rw [chart_toBase]
  infer_instance

/-- The finite affine chart cover makes the assembled scheme quasi-compact. -/
instance scheme_compactSpace : CompactSpace (scheme R t n h) := by
  let U := chartCover R t n h
  let _ : Finite U.I₀ := inferInstanceAs (Finite (Fin n))
  let _ : ∀ i, CompactSpace (U.X i) := fun _ ↦
    PrimeSpectrum.compactSpace (R := ChartRing t)
  exact U.compactSpace

/-- The actual arithmetic structure map is quasi-compact. -/
instance toBase_quasiCompact : QuasiCompact (toBase R t n h) := by
  infer_instance

/-- The assembled family as an object over the original arithmetic base. -/
def family : Over (Spec (.of R)) := Over.mk (toBase R t n h)

end FLT.Mazur.PolygonInfinitesimal
