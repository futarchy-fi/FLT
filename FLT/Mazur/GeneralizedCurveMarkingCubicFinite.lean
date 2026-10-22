/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingAffineCartesian
public import FLT.Mazur.WeierstrassIntegralProper
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finiteness of the original relative cubic morphism

The affine restriction is injective. The remaining points lie on the original
section, where the structural map separates them. Thus the proper cubic
morphism has singleton fibers and is finite, over the entire varying base.

This specialization assumes integral geometric fibers, allowing singular cubics
but excluding higher polygons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  Scheme.Modules.pullback ModuleSheafTensor.tensor

variable {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) [GeometricallyIntegral E.curve.hom]
  (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

local instance generalizedCurveMarkingCubicFiniteProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

local notation "L" => divisorLineBundle (Scheme.Hom.ker (Over.Hom.left (t))) (hI)
local notation "T" => smoothMarkingProjectiveSections E s e
local notation "W" => smoothMarkingWeierstrassCurve E s e
open WeierstrassIntegralChart

local notation "U" => (TopologicalSpace.Closeds.compl (Scheme.IdealSheafData.support
    (Scheme.Hom.ker (Over.Hom.left (t)))) : E.curve.left.Opens)

local notation "f" => smoothMarkingToIntegralCubic E s e

omit [GeometricallyIntegral E.curve.hom] in
/-- The original global cubic map is proper over the actual coefficient spectrum. -/
theorem smoothMarkingToIntegralCubic_proper : IsProper (f) := by
  have h : IsProper ((f) ≫ integralCurveStructure (W)) := by
    rw [smoothMarkingToIntegralCubic_over]
    infer_instance
  exact IsProper.of_comp (f) (integralCurveStructure (W))

/-- The original affine comparison and marked section separate all points of the total space. -/
theorem smoothMarkingToIntegralCubic_injective : Function.Injective (f) := by
  intro x y hxy
  have hmem : x ∈ (U) ↔ y ∈ (U) := by
    rw [← smoothMarkingToIntegralCubic_preimage_z E s e]
    change (f) x ∈ (integralCurveChart (W) 2).opensRange ↔
      (f) y ∈ (integralCurveChart (W) 2).opensRange
    rw [hxy]
  by_cases hx : x ∈ (U)
  · let _ := smoothMarkingToIntegralCubic_affine_isOpenImmersion E s e
    have h := ((Scheme.Opens.ι (X := E.curve.left) (U)) ≫ (f)).isOpenEmbedding.injective
      (show ((Scheme.Opens.ι (X := E.curve.left) (U)) ≫ (f)) ⟨x, hx⟩ =
        ((Scheme.Opens.ι (X := E.curve.left) (U)) ≫ (f)) ⟨y, hmem.mp hx⟩ from hxy)
    exact congrArg Subtype.val h
  · have hy : y ∉ (U) := fun hy ↦ hx (hmem.mpr hy)
    have hx' : x ∈ ((t).left.ker.support : Set E.curve.left) := not_not.mp hx
    have hy' : y ∈ ((t).left.ker.support : Set E.curve.left) := not_not.mp hy
    rw [support_section_ker E.curve.hom (t).left (t).w] at hx' hy'
    obtain ⟨a, rfl⟩ := hx'
    obtain ⟨b, rfl⟩ := hy'
    have hs (z : S) : E.curve.hom ((t).left z) = z :=
      congrArg (fun k : S ⟶ S ↦ k z) (t).w
    have hb : (E.curve.hom ≫ S.toSpecΓ) ((t).left a) =
        (E.curve.hom ≫ S.toSpecΓ) ((t).left b) := by
      rw [← smoothMarkingToIntegralCubic_over E s e]
      exact congrArg (integralCurveStructure (W)) hxy
    have hab : a = b := S.toSpecΓ.isOpenEmbedding.injective (by
      simpa only [Scheme.Hom.comp_apply, hs] using hb)
    exact congrArg (t).left hab

/-- The original cubic factorization is finite, including above the marking. -/
theorem smoothMarkingToIntegralCubic_finite : IsFinite (f) := by
  let _ := smoothMarkingToIntegralCubic_proper E s e
  let _ : LocallyQuasiFinite (f) :=
    LocallyQuasiFinite.of_injective (smoothMarkingToIntegralCubic_injective E s e)
  exact IsFinite.of_isProper_of_locallyQuasiFinite (f)

end FLT.Mazur.GeneralizedEllipticCurve
