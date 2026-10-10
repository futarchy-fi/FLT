/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSupportOpenLattice

/-!
# Full family restriction along ambient inclusions

The morphism between Hilbert support opens classifies the same containing
ambient ideal. Its full family restricts to the original full ideal on the
smaller ambient open; this is an ideal equality, retaining multiplicities.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ) (K : Ideal (MvPolynomial I R))
variable (U V : (Spec (.of (MvPolynomial I R ⧸ K))).Opens) (h : U ≤ V)
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))

/-- An actual Hilbert parameter in a smaller ambient open gives one in a larger ambient open. -/
def openAmbientParameterInclusion (p : OpenAmbientSchemeParameters R I d K U s) :
    OpenAmbientSchemeParameters R I d K V s :=
  ⟨p.val ≫ openAmbientHilbertInclusion R I d K U V h,
    (Category.assoc _ _ _).trans
      ((congrArg (p.val ≫ ·) (openAmbientHilbertInclusion_over R I d K U V h)).trans
        p.property)⟩

/-- In the containing affine Hilbert scheme the two parameters are the same actual morphism. -/
theorem openAmbientParameterInclusion_ambient (p : OpenAmbientSchemeParameters R I d K U s) :
    (openAmbientParameterInclusion R I d K U V h s p).val ≫
        (ambientHilbertSupportOpen R I d K V).ι =
      p.val ≫ (ambientHilbertSupportOpen R I d K U).ι := by
  change (p.val ≫ openAmbientHilbertInclusion R I d K U V h) ≫ _ = _
  rw [Category.assoc, openAmbientHilbertInclusion_ι]

/-- The corresponding inclusion of actual relative ambient opens over the test scheme. -/
def quotientRelativeOpenInclusion :
    (quotientRelativeOpen R I K U s).toScheme ⟶ (quotientRelativeOpen R I K V s).toScheme :=
  (quotientRelativeAmbient R I K s).homOfLE
    (show quotientRelativeOpen R I K U s ≤ quotientRelativeOpen R I K V s from
      fun _ hx ↦ h hx)

/-- Relative ambient inclusion retains its map into the complete affine relative ambient. -/
@[reassoc]
theorem quotientRelativeOpenInclusion_ι :
    quotientRelativeOpenInclusion R I K U V h s ≫ (quotientRelativeOpen R I K V s).ι =
      (quotientRelativeOpen R I K U s).ι := Scheme.homOfLE_ι _ _

/-- Hilbert inclusion recovers the entire original family ideal by actual ambient restriction. -/
theorem openAmbientParameterInclusion_family (p : OpenAmbientSchemeParameters R I d K U s) :
    (openAmbientSchemeClassification R I d K V s
        (openAmbientParameterInclusion R I d K U V h s p)).val.comap
          (quotientRelativeOpenInclusion R I K U V h s) =
      (openAmbientSchemeClassification R I d K U s p).val := by
  rw [openAmbientSchemeClassification_ideal, openAmbientSchemeClassification_ideal,
    ← comap_comp, quotientRelativeOpenInclusion_ι]
  apply congrArg (fun f : AmbientSchemeParameters R I d K s ↦
    (ambientSchemeClassification R I d K s f).val.comap (quotientRelativeOpen R I K U s).ι)
  apply Subtype.ext
  exact openAmbientParameterInclusion_ambient R I d K U V h s p

end FLT.Mazur.HilbertChart
