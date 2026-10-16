/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineChartOpenSectionTransport
public import FLT.Mazur.DivisorChartPoleRatio

/-!
# Bounded canonical numerators in an original affine localization

An affine map through the actual Cartier complement carries the original
numerator identity into its coordinate ring, retaining the canonical frame.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback AffineImmersionSectionCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
universe u
variable {X : Scheme.{u}} {I : X.IdealSheafData} (hI : EffectiveCartier I)
variable {A B : Type u} [CommRing A] [CommRing B]
variable (f : Spec (.of A) ⟶ X) [IsOpenImmersion f]
local notation "U" => imageAffine f
local notation "C" => (I.support.compl : X.Opens)
local notation "L" => divisorLineBundle I hI

/-- The specified coordinate map clears the actual complement function in its own degree. -/
theorem divisorAffineLocalizedNumerator (a : Γ(X, (U).1)) (ha : IsRegular a)
    (he : I.ideal (U) = Ideal.span {a}) (σ : A →+* B)
    (q : Spec (.of B) ⟶ (Scheme.Opens.toScheme (X := X) (C)))
    (hq : Spec.map (CommRingCat.ofHom σ) ≫ f = q ≫ (Scheme.Opens.ι (X := X) (C)))
    (d : ℕ) (hd : 0 < d) (s : Γ(tensorPower (L) d, ⊤)) :
    σ (coordinates f a) ^ d *
      (Scheme.ΓSpecIso (.of B)).hom (q.appTop (divisorComplementFunction hI d s)) =
      σ (coordinates f (divisorChartTensorNumerator hI (U) a ha he d
        ((tensorPower (L) d).presheaf.map (U).1.leTop.op s))) := by
  let b := q ≫ (Scheme.Opens.ι (X := X) (C))
  let V : X.Opens := (U).1 ⊓ (C)
  have hV : ⊤ ≤ b ⁻¹ᵁ V := by
    intro x _
    constructor
    · exact ⟨Spec.map (CommRingCat.ofHom σ) x, trivial,
        congrArg (fun k : Spec (.of B) ⟶ X ↦ k x) hq⟩
    · exact (q x).property
  let e : Γ(X, V) →+* B := (Scheme.ΓSpecIso (.of B)).hom.hom.comp
    (b.appLE V ⊤ hV).hom
  have hU : ⊤ ≤ b ⁻¹ᵁ (U).1 := hV.trans (by exact fun _ hx ↦ hx.1)
  have hC : ⊤ ≤ b ⁻¹ᵁ (C) := hV.trans (by exact fun _ hx ↦ hx.2)
  have eU (z : Γ(X, (U).1)) :
      e (X.presheaf.map (homOfLE (show V ≤ (U).1 from inf_le_left)).op z) =
        σ (coordinates f z) := by
    change (Scheme.ΓSpecIso (.of B)).hom
      ((X.presheaf.map _ ≫ b.appLE V ⊤ hV) z) = _
    rw [Scheme.Hom.map_appLE]
    exact coordinates_appLE f σ b hq hU z
  have eC (z : Γ(X, (C))) :
      e (X.presheaf.map (homOfLE (show V ≤ (C) from inf_le_right)).op z) =
        (Scheme.ΓSpecIso (.of B)).hom (q.appTop ((Scheme.Opens.topIso (X := X) (C)).inv z)) := by
    change (Scheme.ΓSpecIso (.of B)).hom
      ((X.presheaf.map _ ≫ b.appLE V ⊤ hV) z) = _
    rw [Scheme.Hom.map_appLE]
    exact congrArg (fun k ↦ (Scheme.ΓSpecIso (.of B)).hom (k z))
      (openFactor_appTop (C) q hC).symm
  have hn := congrArg e (divisorChartTensorNumerator_complement_ratio hI (U)
    a ha he d hd V inf_le_left inf_le_right s)
  rw [map_mul, map_pow, eU, eU] at hn
  rw [divisorComplementFunction_eq_ratio hI d hd]
  rw [← eC, sectionRatioOn_restrict]
  exact hn

end FLT.Mazur.FCurve
