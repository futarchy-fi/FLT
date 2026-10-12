/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneAffineCartesian
public import FLT.Mazur.WeierstrassIntegralProper
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finiteness of the original relative cubic morphism

The affine restriction is injective. The remaining points lie on the original
section, where the structural map separates them. Thus the proper cubic
morphism has singleton fibers and is finite, over the entire varying base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates

variable {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

local notation "L" => divisorLineBundle s.left.ker hI
local notation "T" => relativePointProjectiveSections G hg s hI e
local notation "W" => relativePointWeierstrassCurve G hg s hI e
open WeierstrassIntegralChart

local notation "U" => (s.left.ker.support.compl : G.left.Opens)

local notation "f" => relativePointToIntegralCubic G hg s hI e

/-- The original global cubic map is proper over the actual coefficient spectrum. -/
theorem relativePointToIntegralCubic_proper : IsProper (f) := by
  have h : IsProper ((f) ≫ integralCurveStructure (W)) := by
    rw [relativePointToIntegralCubic_over]
    infer_instance
  exact IsProper.of_comp (f) (integralCurveStructure (W))

/-- The original affine comparison and marked section separate all points of the total space. -/
theorem relativePointToIntegralCubic_injective : Function.Injective (f) := by
  intro x y hxy
  have hmem : x ∈ (U) ↔ y ∈ (U) := by
    rw [← relativePointToIntegralCubic_preimage_z G hg s hI e]
    change (f) x ∈ (integralCurveChart (W) 2).opensRange ↔
      (f) y ∈ (integralCurveChart (W) 2).opensRange
    rw [hxy]
  by_cases hx : x ∈ (U)
  · let _ := relativePointToIntegralCubic_affine_isOpenImmersion G hg s hI e
    have h := ((Scheme.Opens.ι (X := G.left) (U)) ≫ (f)).isOpenEmbedding.injective
      (show ((Scheme.Opens.ι (X := G.left) (U)) ≫ (f)) ⟨x, hx⟩ =
        ((Scheme.Opens.ι (X := G.left) (U)) ≫ (f)) ⟨y, hmem.mp hx⟩ from hxy)
    exact congrArg Subtype.val h
  · have hy : y ∉ (U) := fun hy ↦ hx (hmem.mpr hy)
    have hx' : x ∈ (s.left.ker.support : Set G.left) := not_not.mp hx
    have hy' : y ∈ (s.left.ker.support : Set G.left) := not_not.mp hy
    rw [support_section_ker G.hom s.left s.w] at hx' hy'
    obtain ⟨a, rfl⟩ := hx'
    obtain ⟨b, rfl⟩ := hy'
    have hs (z : S) : G.hom (s.left z) = z :=
      congrArg (fun k : S ⟶ S ↦ k z) s.w
    have hb : (G.hom ≫ S.toSpecΓ) (s.left a) =
        (G.hom ≫ S.toSpecΓ) (s.left b) := by
      rw [← relativePointToIntegralCubic_over G hg s hI e]
      exact congrArg (integralCurveStructure (W)) hxy
    have hab : a = b := S.toSpecΓ.isOpenEmbedding.injective (by
      simpa only [Scheme.Hom.comp_apply, hs] using hb)
    exact congrArg s.left hab

/-- The original cubic factorization is finite, including above the marking. -/
theorem relativePointToIntegralCubic_finite : IsFinite (f) := by
  let _ := relativePointToIntegralCubic_proper G hg s hI e
  let _ : LocallyQuasiFinite (f) :=
    LocallyQuasiFinite.of_injective (relativePointToIntegralCubic_injective G hg s hI e)
  exact IsFinite.of_isProper_of_locallyQuasiFinite (f)

end FLT.Mazur.FCurve
