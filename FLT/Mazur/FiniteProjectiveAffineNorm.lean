/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineNormGluingFiber
public import FLT.Mazur.FiniteProjectiveAffineNormCharts

/-!
# The norm of an original finite projective affine morphism

Local bases are constructed from finite projectivity and glued in the actual
structure sheaf. The resulting multiplicative norm has the full-fiber test
without requiring the original section algebra to have a global basis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteProjectiveAffineNorm
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
variable (hf : let _ := f.appTop.hom.toAlgebra; Module.Finite Γ(Y, ⊤) Γ(X, ⊤))
  (hp : let _ := f.appTop.hom.toAlgebra; Module.Projective Γ(Y, ⊤) Γ(X, ⊤))

/-- A genuine finite free chart around each original target point. -/
def chart (y : Y) : Y.affineOpens :=
  (FiniteProjectiveAffineNormCharts.exists_chart f y hf hp).choose

/-- Each chosen chart contains the point it was constructed around. -/
theorem mem_chart (y : Y) : y ∈ (chart f hf hp y).1 :=
  (FiniteProjectiveAffineNormCharts.exists_chart f y hf hp).choose_spec.1

/-- The basis describes the entire original preimage, not a finite envelope. -/
theorem chart_basis (y : Y) : AffineOpenNorm.HasBasis f (chart f hf hp y) :=
  (FiniteProjectiveAffineNormCharts.exists_chart f y hf hp).choose_spec.2

/-- The constructed free charts cover the entire target. -/
theorem chart_cover : ⨆ y, (chart f hf hp y).1 = ⊤ := by
  apply top_unique
  intro y _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, mem_chart f hf hp y⟩

/-- The multiplicative norm obtained from actual local finite bases. -/
def norm : Γ(X, ⊤) →* Γ(Y, ⊤) :=
  AffineNormGluing.normHom f (chart f hf hp) (chart_basis f hf hp) (chart_cover f hf hp)

/-- The norm computes the usual determinant on any genuine free affine chart. -/
theorem norm_restrict (U : Y.affineOpens) (hU : AffineOpenNorm.HasBasis f U)
    (s : Γ(X, ⊤)) :
    Y.presheaf.map (homOfLE le_top).op (norm f hf hp s) = AffineNormGluing.chart f U s :=
  AffineNormGluing.norm_any_chart f (chart f hf hp) (chart_basis f hf hp)
    (chart_cover f hf hp) U hU s

/-- Nonvanishing of the finite projective norm tests every point of the original fiber. -/
theorem mem_basicOpen_norm_iff (s : Γ(X, ⊤)) (y : Y) :
    y ∈ Y.basicOpen (norm f hf hp s) ↔ ∀ x : X, f x = y → x ∈ X.basicOpen s :=
  AffineNormGluing.mem_basicOpen_norm_iff f (chart f hf hp) (chart_basis f hf hp)
    (chart_cover f hf hp) s y

end FLT.Mazur.FiniteProjectiveAffineNorm
