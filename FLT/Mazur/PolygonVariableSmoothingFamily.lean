/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonVariableSmoothingAtlas
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

namespace FLT.Mazur.PolygonVariableSmoothing

set_option backward.isDefEq.respectTransparency false

open PolygonSmoothing

variable (R : Type u) [CommRing R] (n : ℕ) (t : Fin n → R)

/-- The compatible original coefficient maps on the arithmetic cyclic diagram. -/
def baseCocone : Cocone (diagram R n t) where
  pt := Spec (.of R)
  ι.app j := match j with
    | .left _ => Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹]))
    | .right i => chartStructure R (t i)
  ι.naturality := by
    intro i j f
    cases f with
    | id i => simp
    | fst i => exact (leftBranchOpen_base R (t i)).trans (Category.comp_id _).symm
    | snd i =>
      exact (precedingBranch_base R (t ((finRotate n).symm i))).trans (Category.comp_id _).symm

variable [∀ i, Fact (IsNilpotent (t i))] (h : 2 ≤ n)

/-- The structure morphism of the actual glued arithmetic scheme. -/
def toBase : scheme R n t h ⟶ Spec (.of R) :=
  letI : Fact (2 ≤ n) := ⟨h⟩
  colimit.desc (diagram R n t) (baseCocone R n t)

/-- Every chart retains its original arithmetic structure morphism. -/
@[reassoc (attr := simp)] theorem chart_toBase (i : Fin n) :
    chart R n t h i ≫ toBase R n t h = chartStructure R (t i) := by
  let : Fact (2 ≤ n) := ⟨h⟩
  exact colimit.ι_desc (baseCocone R n t) (.right i)

/-- The original smoothing charts form a finite affine open cover. -/
def chartCover : (scheme R n t h).OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (Fin n)
    (fun i ↦ PolygonSmoothing.chart R (t i)) (chart R n t h)
    (fun x ↦ by
      obtain ⟨i, y, hy⟩ := charts_cover R n t h x
      exact ⟨i, y, hy⟩) (fun _ ↦ inferInstance)

/-- The assembled infinitesimal polygon is flat over its actual coefficient base. -/
instance toBase_flat : Flat (toBase R n t h) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (chartCover R n t h)).mpr
  intro i
  change Flat (chart R n t h i ≫ toBase R n t h)
  rw [chart_toBase]
  infer_instance

/-- The assembled infinitesimal polygon is locally finitely presented over its base. -/
instance toBase_locallyOfFinitePresentation : LocallyOfFinitePresentation (toBase R n t h) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (chartCover R n t h)).mpr
  intro i
  change LocallyOfFinitePresentation (chart R n t h i ≫ toBase R n t h)
  rw [chart_toBase]
  infer_instance

/-- The finite affine chart cover makes the assembled scheme quasi-compact. -/
instance scheme_compactSpace : CompactSpace (scheme R n t h) := by
  let U := chartCover R n t h
  let _ : Finite U.I₀ := inferInstanceAs (Finite (Fin n))
  let _ : ∀ i, CompactSpace (U.X i) := fun i ↦
    PrimeSpectrum.compactSpace (R := ChartRing (t i))
  exact U.compactSpace

/-- The actual arithmetic structure map is quasi-compact. -/
instance toBase_quasiCompact : QuasiCompact (toBase R n t h) := by
  infer_instance

/-- The assembled family as an object over the original arithmetic base. -/
def family : Over (Spec (.of R)) := Over.mk (toBase R n t h)

end FLT.Mazur.PolygonVariableSmoothing
