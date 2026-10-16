/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorTensorNumeratorOverlap
public import FLT.Mazur.AffineChartOpenSectionTransport

/-!
# Bounded numerator compatibility in actual affine overlap coordinates

Any affine overlap mapping to both original charts inherits the exact
cross-multiplied numerator equation over its unchanged coordinate ring.
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
variable {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
variable (f : Spec (.of A) ⟶ X) (g : Spec (.of B) ⟶ X)
  [IsOpenImmersion f] [IsOpenImmersion g]
local notation "U" => imageAffine f
local notation "V" => imageAffine g
local notation "L" => divisorLineBundle I hI

/-- Original affine overlap maps give the full coefficient-level numerator equation. -/
theorem divisorAffineNumerator_overlap
    (a : Γ(X, (U).1)) (b : Γ(X, (V).1)) (ha : IsRegular a) (hb : IsRegular b)
    (he : I.ideal (U) = Ideal.span {a}) (hf : I.ideal (V) = Ideal.span {b})
    (σ : A →+* D) (τ : B →+* D)
    (hq : Spec.map (CommRingCat.ofHom σ) ≫ f = Spec.map (CommRingCat.ofHom τ) ≫ g)
    (d : ℕ) (s : Γ(tensorPower (L) d, ⊤)) :
    σ (coordinates f a) ^ d * τ (coordinates g
      (divisorChartTensorNumerator hI (V) b hb hf d
        ((tensorPower (L) d).presheaf.map (V).1.leTop.op s))) =
    τ (coordinates g b) ^ d * σ (coordinates f
      (divisorChartTensorNumerator hI (U) a ha he d
        ((tensorPower (L) d).presheaf.map (U).1.leTop.op s))) := by
  let q := Spec.map (CommRingCat.ofHom σ) ≫ f
  let W : X.Opens := (U).1 ⊓ (V).1
  have hW : ⊤ ≤ q ⁻¹ᵁ W := by
    intro x _
    constructor
    · exact ⟨Spec.map (CommRingCat.ofHom σ) x, trivial, rfl⟩
    · exact ⟨Spec.map (CommRingCat.ofHom τ) x, trivial,
        congrArg (fun k : Spec (.of D) ⟶ X ↦ k x) hq.symm⟩
  let e : Γ(X, W) →+* D := (Scheme.ΓSpecIso (.of D)).hom.hom.comp
    (q.appLE W ⊤ hW).hom
  have eU (z : Γ(X, (U).1)) :
      e (X.presheaf.map (homOfLE (show W ≤ (U).1 from inf_le_left)).op z) =
        σ (coordinates f z) := by
    change (Scheme.ΓSpecIso (.of D)).hom
      ((X.presheaf.map _ ≫ q.appLE W ⊤ hW) z) = _
    rw [Scheme.Hom.map_appLE]
    exact coordinates_appLE f σ q rfl _ z
  have eV (z : Γ(X, (V).1)) :
      e (X.presheaf.map (homOfLE (show W ≤ (V).1 from inf_le_right)).op z) =
        τ (coordinates g z) := by
    change (Scheme.ΓSpecIso (.of D)).hom
      ((X.presheaf.map _ ≫ q.appLE W ⊤ hW) z) = _
    rw [Scheme.Hom.map_appLE]
    exact coordinates_appLE g τ q hq.symm _ z
  have hn := congrArg e (divisorChartTensorNumerator_overlap hI (U) (V)
    a b ha hb he hf d s W inf_le_left inf_le_right)
  simpa only [map_mul, map_pow, eU, eV] using hn

end FLT.Mazur.FCurve
