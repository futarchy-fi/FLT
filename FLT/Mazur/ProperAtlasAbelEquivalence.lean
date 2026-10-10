/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperTwistedLineDescent
public import FLT.Mazur.ProperAtlasAbelFiber

/-!
# The actual direct-image atlas represents the relative Cartier Abel fiber

Unpointed descent identifies the retained base-line relation with the full
total-space section relation. Thus the previously constructed surjection
from actual projective-atlas sections is injective and is an equivalence.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve
variable {X S : Scheme.{0}} (f : X ⟶ S) (L : X.Modules)
  [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsProper f] [Flat f]
  [Surjective f] [GeometricallyIntegral f] (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (LineSectionBaseChange.residueAlgebraFiberLine f L z) (n + 1)))

/-- Retained base-line orbits are exactly the original total-space section orbits. -/
theorem relativeBaseLineSetoid_iff_sectionSetoid (s t : RelativeSection f L hL) :
    (relativeBaseLineSetoid f L hL hV).r s t ↔ (relativeSectionSetoid f L hL).r s t := by
  let _ : IsLocallyNoetherian S := isLocallyNoetherian_of_affine_cover
    (S := fun _ : Unit ↦ ⟨⊤, isAffineOpen_top S⟩) (by simp) (fun _ ↦ inferInstance)
  let _ : GeometricallyConnected f := ⟨by
    intro K _ a Y p q H
    let _ := GeometricallyIntegral.geometrically_isIntegral (f := f) a p q H
    infer_instance⟩
  exact (relativeBaseLineSetoid_iff_iso f L hL hV s t).trans
    (ProperLineIsomorphismDescent.sectionSetoid_iff_baseIso f L hL s.val t.val).symm

/-- The full relative Cartier divisor detects equality in the actual projective atlas. -/
theorem relativeSection_toAtlas_eq_iff_fiber (s t : RelativeSection f L hL) :
    s.toAtlas f L hL hV = t.toAtlas f L hL hV ↔
      relativeSectionToFiber f L hL s = relativeSectionToFiber f L hL t :=
  (relativeSection_toAtlas_eq_iff f L hL hV s t).trans
    ((relativeBaseLineSetoid_iff_sectionSetoid f L hL hV s t).trans
      (relativeSectionToFiber_eq_iff f L hL s t).symm)

/-- Different actual atlas sections give different full relative Abel divisors. -/
theorem atlasToRelativeFiber_injective : Function.Injective (atlasToRelativeFiber f L hL hV) := by
  intro a b hab
  obtain ⟨s, rfl⟩ := relativeSection_toAtlas_surjective f L hL hV a
  obtain ⟨t, rfl⟩ := relativeSection_toAtlas_surjective f L hL hV b
  rw [atlasToRelativeFiber_toAtlas, atlasToRelativeFiber_toAtlas] at hab
  exact (relativeSection_toAtlas_eq_iff_fiber f L hL hV s t).mpr hab

/-- Actual projective-atlas sections are exactly the relative Cartier Abel fiber. -/
def atlasRelativeFiberEquiv : DirectImageAtlasSection f L hL hV ≃ RelativeFiber f L hL :=
  Equiv.ofBijective (atlasToRelativeFiber f L hL hV)
    ⟨atlasToRelativeFiber_injective f L hL hV, atlasToRelativeFiber_surjective f L hL hV⟩

/-- The equivalence sends an original relative section to its full original zero divisor. -/
lemma atlasRelativeFiberEquiv_toAtlas (s : RelativeSection f L hL) :
    atlasRelativeFiberEquiv f L hL hV (s.toAtlas f L hL hV) =
      relativeSectionToFiber f L hL s := atlasToRelativeFiber_toAtlas f L hL hV s

/-- Recovering the atlas point of an original divisor retains its original section class. -/
lemma atlasRelativeFiberEquiv_symm_section (s : RelativeSection f L hL) :
    (atlasRelativeFiberEquiv f L hL hV).symm (relativeSectionToFiber f L hL s) =
      s.toAtlas f L hL hV := by
  rw [← atlasRelativeFiberEquiv_toAtlas f L hL hV s, Equiv.symm_apply_apply]

end FLT.Mazur.CartierAbel
