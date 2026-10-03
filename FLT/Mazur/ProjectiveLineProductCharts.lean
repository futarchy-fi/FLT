/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineCharts
public import FLT.Mazur.MultiplicativeGroupScheme
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.AlgebraicGeometry.Pullbacks
/-!
# Polynomial charts after an affine parameter base change

The product with an arbitrary affine parameter scheme has two charts with
coordinate ring S[X]. The projection formulas identify both factors, and
the transported open cover covers the whole fiber product. Laurent parameters
give the charts needed for the relative multiplicative action.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Polynomial LaurentPolynomial TensorProduct
universe u
namespace FLT.Mazur.ProjectiveLineProductCharts
variable (K S : Type u) [Field K] [CommRing S] [Algebra K S]

/-- The affine parameter scheme over the coefficient field. -/
def parameterToBase : Spec (.of S) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K S))

/-- The product of the parameter scheme with an affine chart. -/
def chartProductIso : pullback (parameterToBase K S) (ProjectiveLine.chartToBase K) ≅
    Spec (.of S[X]) :=
  pullbackSpecIso K S K[X] ≪≫
    Scheme.Spec.mapIso (polyEquivTensor' K S).toRingEquiv.toCommRingCatIso.op

@[reassoc (attr := simp)]
theorem chartProductIso_inv_fst :
    (chartProductIso K S).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S S[X])) := by
  change Spec.map (CommRingCat.ofHom (polyEquivTensor' K S).symm.toAlgHom.toRingHom) ≫
    (pullbackSpecIso K S K[X]).inv ≫ pullback.fst _ _ = _
  rw [pullbackSpecIso_inv_fst']
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact AlgHom.comp_algebraMap (polyEquivTensor' K S).symm.toAlgHom

@[reassoc (attr := simp)]
theorem chartProductIso_inv_snd :
    (chartProductIso K S).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap K S))) := by
  change Spec.map (CommRingCat.ofHom (polyEquivTensor' K S).symm.toAlgHom.toRingHom) ≫
    (pullbackSpecIso K S K[X]).inv ≫ pullback.snd _ _ = _
  rw [pullbackSpecIso_inv_snd]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact one_smul S (p.map (algebraMap K S))

/-- The two affine charts of the specified glued projective line. -/
def chartCover : (ProjectiveLine.scheme K).OpenCover where
  I₀ := Bool
  X _ := ProjectiveLine.chart K
  f b := if b then ProjectiveLine.right K else ProjectiveLine.left K
  mem₀ := by
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨?_, ?_⟩
    · intro x
      rcases ProjectiveLine.charts_cover K x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨false, y, hy⟩
      · exact ⟨true, y, hy⟩
    · intro b
      cases b <;> dsimp <;> infer_instance

@[reassoc (attr := simp)]
theorem chartCover_toBase (b : Bool) :
    (chartCover K).f b ≫ ProjectiveLine.toBase K = ProjectiveLine.chartToBase K := by
  cases b <;> simp [chartCover]

/-- The parameter scheme times the projective line over the coefficient field. -/
abbrev product := pullback (parameterToBase K S) (ProjectiveLine.toBase K)

/-- Pull back the projective-line cover along the parameter base change. -/
def productPullbackCover : (product K S).OpenCover :=
  Scheme.Pullback.openCoverOfRight (chartCover K) (parameterToBase K S)
    (ProjectiveLine.toBase K)

/-- Polynomial coordinates on each member of the pulled-back cover. -/
def productChartIso (b : Bool) : (productPullbackCover K S).X b ≅ Spec (.of S[X]) :=
  pullback.congrHom rfl (chartCover_toBase K b) ≪≫ chartProductIso K S

/-- The polynomial chart maps into the full product. -/
def productChartMap (b : Bool) : Spec (.of S[X]) ⟶ product K S :=
  (productChartIso K S b).inv ≫ (productPullbackCover K S).f b

instance productChartMap_isOpenImmersion (b : Bool) :
    IsOpenImmersion (productChartMap K S b) := by
  unfold productChartMap
  infer_instance

@[reassoc (attr := simp)]
theorem productChartMap_fst (b : Bool) :
    productChartMap K S b ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S S[X])) := by
  simp [productChartMap, productChartIso, productPullbackCover,
    Scheme.Pullback.openCoverOfRight_f]

@[reassoc (attr := simp)]
theorem productChartMap_snd (b : Bool) :
    productChartMap K S b ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap K S))) ≫
        (chartCover K).f b := by
  simp [productChartMap, productChartIso, productPullbackCover,
    Scheme.Pullback.openCoverOfRight_f]

/-- An open cover of the full product by the two polynomial spectra. -/
def productChartCover : (product K S).OpenCover :=
  (productPullbackCover K S).copy Bool (fun _ ↦ Spec (.of S[X]))
    (productChartMap K S) (Equiv.refl _) (fun b ↦ (productChartIso K S b).symm)
    (fun _ ↦ rfl)

theorem iSup_productChartMap_opensRange :
    ⨆ b : Bool, (productChartMap K S b).opensRange = ⊤ :=
  (productChartCover K S).iSup_opensRange

/-- The Laurent-parameter instance used by the multiplicative group action. -/
abbrev gmChartProductIso :
    pullback (MultiplicativeGroupScheme.gm K).hom (ProjectiveLine.chartToBase K) ≅
      Spec (.of K[T;T⁻¹][X]) := chartProductIso K K[T;T⁻¹]
end FLT.Mazur.ProjectiveLineProductCharts
