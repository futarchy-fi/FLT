/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommonAmbientSourceGrassmannianImmersion
public import FLT.Mazur.VariableHilbertCommonAmbientAtlas
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Actual affine source charts from the finite Grassmannian immersion

Affine opens of the canonical closed-factor target pull back to actual affine
opens of the unrestricted original source. These form a cover and retain the
common ambient support condition. No one chart is asserted to contain an
entire orbit, and no invariance is inferred from affineness.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
open FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ) (V : Over (Spec (.of R)))
  (U : X.affineOpens)
local notation "N" => commonAmbientSourceGrassmannianNeighborhood f d V U

/-- An actual affine chart of the original source, obtained through its closed immersion. -/
def commonAmbientGrassmannianSourceOpen (W : (N).toScheme.affineOpens) :
    (variableHilbertTest f d V).left.Opens :=
  (commonAmbientSourceInclusion f d V U).left ''ᵁ
    (commonAmbientSourceGrassmannianClosedFactor f d V U ⁻¹ᵁ W.val)

/-- Closed pullback and open inclusion prove affineness of this original source open. -/
theorem commonAmbientGrassmannianSourceOpen_isAffine (W : (N).toScheme.affineOpens) :
    IsAffineOpen (commonAmbientGrassmannianSourceOpen f d V U W) := by
  have hW := W.property.preimage (commonAmbientSourceGrassmannianClosedFactor f d V U)
  exact hW.image_of_isOpenImmersion (commonAmbientSourceInclusion f d V U).left

/-- Every constructed affine open remains supported in its original common ambient. -/
theorem commonAmbientGrassmannianSourceOpen_le (W : (N).toScheme.affineOpens) :
    commonAmbientGrassmannianSourceOpen f d V U W ≤ commonAmbientSourceOpen f d V U := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

/-- These genuine affine charts cover each whole common-ambient source neighborhood. -/
theorem exists_commonAmbientGrassmannianSourceOpen
    (x : (variableHilbertTest f d V).left) (hx : x ∈ commonAmbientSourceOpen f d V U) :
    ∃ W : (N).toScheme.affineOpens, x ∈ commonAmbientGrassmannianSourceOpen f d V U W := by
  let y : (commonAmbientSourceTest f d V U).left := ⟨x, hx⟩
  obtain ⟨W, hW, hy, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := commonAmbientSourceGrassmannianClosedFactor f d V U y) (U := ⊤) trivial
  exact ⟨⟨W, hW⟩, y, hy, rfl⟩

variable {L : X.Modules} (hL : AmpleLineBundle L)

/-- An affine cover of the unrestricted original source, constructed from finite immersions. -/
def commonAmbientGrassmannianAffineCover : (variableHilbertTest f d V).left.OpenCover where
  I₀ := (U : X.affineOpens) ×
    (commonAmbientSourceGrassmannianNeighborhood f d V U).toScheme.affineOpens
  X i := (commonAmbientGrassmannianSourceOpen f d V i.1 i.2).toScheme
  f i := (commonAmbientGrassmannianSourceOpen f d V i.1 i.2).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ inferInstance⟩
    obtain ⟨U, hU⟩ := exists_commonAmbientSourceOpen f d V hL {x} (Set.finite_singleton x)
    obtain ⟨W, hx⟩ := exists_commonAmbientGrassmannianSourceOpen f d V U x
      (hU (Set.mem_singleton x))
    exact ⟨⟨U, W⟩, ⟨x, hx⟩, rfl⟩

instance (i : (commonAmbientGrassmannianAffineCover f d V hL).I₀) :
    IsAffine ((commonAmbientGrassmannianAffineCover f d V hL).X i) :=
  commonAmbientGrassmannianSourceOpen_isAffine f d V i.1 i.2

end FLT.Mazur.HilbertChart
