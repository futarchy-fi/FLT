/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothAffineTransport
public import FLT.Mazur.WeierstrassSmoothPolynomialDomain
public import FLT.Mazur.WeierstrassMixedProductCover

/-!
# Covering every smooth mixed input pair in arbitrary reduction

When at least one input uses the affine chart, the smooth affine overlap and
the smooth polynomial output-Z domain cover the entire smooth input product.
The cover is formed from the original domains and needs no unit discriminant.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (b c : Bool)

/-- The simultaneous affine overlap as an open subscheme of the smooth input product. -/
def smoothAffineOverlapToChart :
    (smoothAffineOverlapOpen W b c).toScheme ⟶ (smoothProductChartOpen W b c).toScheme :=
  IsOpenImmersion.lift (smoothProductChartOpen W b c).ι (smoothAffineOverlapInput W b c) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    exact (smoothAffineOverlapOpen_eq W b c).le p.property)

/-- The restricted affine overlap keeps its original input inclusion. -/
@[reassoc] theorem smoothAffineOverlapToChart_inclusion :
    smoothAffineOverlapToChart W b c ≫ (smoothProductChartOpen W b c).ι =
      smoothAffineOverlapInput W b c :=
  IsOpenImmersion.lift_fac _ _ _

/-- The simultaneous smooth affine overlap remains open after restriction. -/
instance smoothAffineOverlapToChart_isOpenImmersion :
    IsOpenImmersion (smoothAffineOverlapToChart W b c) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift _ _ _))

/-- The two actual smooth domains used to cover a mixed input chart. -/
def smoothMixedDomain : Bool → Scheme.{u}
  | true => (smoothAffineOverlapOpen W b c).toScheme
  | false => (polynomialSmoothInputOpen W
      (productChartCoordinate b) (productChartCoordinate c) 2).toScheme

/-- The original domain inclusions restricted to smooth inputs. -/
def smoothMixedInclusion (d : Bool) :
    smoothMixedDomain W b c d ⟶ (smoothProductChartOpen W b c).toScheme :=
  match d with
  | true => smoothAffineOverlapToChart W b c
  | false => smoothPolynomialToInputs W b c 2

/-- Both members of the smooth mixed cover are open immersions. -/
instance smoothMixedInclusion_isOpenImmersion (d : Bool) :
    IsOpenImmersion (smoothMixedInclusion W b c d) := by
  cases d <;> dsimp [smoothMixedInclusion] <;> infer_instance

/-- Every smooth pair with an affine input belongs to one of the two original domains. -/
theorem smoothMixedInclusion_covers (ha : b = false ∨ c = false)
    (p : (smoothProductChartOpen W b c).toScheme) :
    ∃ d, p ∈ Set.range (smoothMixedInclusion W b c d) := by
  have hb : productChartCoordinate b = 1 ∨ productChartCoordinate b = 2 := by
    cases b <;> simp [productChartCoordinate]
  have hc : productChartCoordinate c = 1 ∨ productChartCoordinate c = 2 := by
    cases c <;> simp [productChartCoordinate]
  have hab : productChartCoordinate b = 2 ∨ productChartCoordinate c = 2 := by
    rcases ha with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨d, q, hq⟩ := mixedProductCoverInclusion_covers W
    (productChartCoordinate b) (productChartCoordinate c) hb hc hab p.val
  cases d with
  | true =>
    have hq' : integralProductOverlapFst W b c false false q = p.val := hq
    have hs : q ∈ smoothAffineOverlapOpen W b c := by
      rw [smoothAffineOverlapOpen_eq]
      change integralProductOverlapFst W b c false false q ∈ smoothProductChartOpen W b c
      rw [hq']
      exact p.property
    refine ⟨true, ⟨q, hs⟩, ?_⟩
    apply (smoothProductChartOpen W b c).ι.isOpenEmbedding.injective
    exact (congrArg (fun f => f ⟨q, hs⟩)
      (smoothAffineOverlapToChart_inclusion W b c)).trans hq'
  | false =>
    have hq' : projectiveAdditionInclusion W
        (productChartCoordinate b) (productChartCoordinate c) 2 q = p.val := hq
    have hs : q ∈ polynomialSmoothInputOpen W
        (productChartCoordinate b) (productChartCoordinate c) 2 := by
      rw [← polynomialSmoothInputOpen_preimage]
      change projectiveAdditionInclusion W
        (productChartCoordinate b) (productChartCoordinate c) 2 q ∈ smoothProductChartOpen W b c
      rw [hq']
      exact p.property
    refine ⟨false, ⟨q, hs⟩, ?_⟩
    apply (smoothProductChartOpen W b c).ι.isOpenEmbedding.injective
    exact (congrArg (fun f => f ⟨q, hs⟩)
      (smoothPolynomialToInputs_inclusion W b c 2)).trans hq'

/-- A complete two-member cover of every smooth mixed input chart product. -/
def smoothMixedCover (ha : b = false ∨ c = false) :
    (smoothProductChartOpen W b c).toScheme.OpenCover where
  I₀ := Bool
  X := smoothMixedDomain W b c
  f := smoothMixedInclusion W b c
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨smoothMixedInclusion_covers W b c ha, fun _ => inferInstance⟩

end FLT.Mazur.WeierstrassIntegralChart
