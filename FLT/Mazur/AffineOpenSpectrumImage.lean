/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Spectrum images of inclusions between affine opens

The range of the coefficient-spectrum map is exactly the smaller original
base open, after the canonical affine spectrum identification.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur
variable {S : Scheme} (U W : S.Opens) [IsAffine U.toScheme] [IsAffine W.toScheme]
  (h : W ≤ U)

/-- The coefficient-spectrum inclusion retains the actual affine base inclusion. -/
theorem affineOpenSpectrumMap_eq :
    Spec.map (S.homOfLE h).appTop =
      W.toScheme.isoSpec.inv ≫ S.homOfLE h ≫ U.toScheme.isoSpec.hom := by
  rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]

/-- Membership in its image is membership in the smaller original base open. -/
theorem mem_affineOpenSpectrumMap_range (x : Spec Γ(U.toScheme, ⊤)) :
    x ∈ Set.range (Spec.map (S.homOfLE h).appTop) ↔
      U.ι (U.toScheme.isoSpec.inv x) ∈ W := by
  have hi (y : W.toScheme) :
      U.ι (S.homOfLE h y) = W.ι y :=
    congrArg (fun f : W.toScheme ⟶ S ↦ f y) (Scheme.homOfLE_ι S h)
  have hinv (y : U.toScheme) :
      U.toScheme.isoSpec.inv (U.toScheme.isoSpec.hom y) = y :=
    congrArg (fun f : U.toScheme ⟶ U.toScheme ↦ f y) U.toScheme.isoSpec.hom_inv_id
  constructor
  · rintro ⟨y, rfl⟩
    rw [affineOpenSpectrumMap_eq U W h]
    simp only [Scheme.Hom.comp_apply, hinv, hi]
    exact (W.toScheme.isoSpec.inv y).property
  · intro hx
    let y : W.toScheme := ⟨U.ι (U.toScheme.isoSpec.inv x), hx⟩
    refine ⟨W.toScheme.isoSpec.hom y, ?_⟩
    apply U.toScheme.isoSpec.inv.isOpenEmbedding.injective
    rw [affineOpenSpectrumMap_eq U W h]
    simp only [Scheme.Hom.comp_apply, hinv]
    have hw : W.toScheme.isoSpec.inv (W.toScheme.isoSpec.hom y) = y :=
      congrArg (fun f : W.toScheme ⟶ W.toScheme ↦ f y) W.toScheme.isoSpec.hom_inv_id
    rw [hw]
    apply U.ι.isOpenEmbedding.injective
    exact hi y

/-- An isomorphism of the source leaves the range of a scheme map unchanged. -/
theorem scheme_range_comp_of_isIso {X Y Z : Scheme} (f : X ⟶ Y) [IsIso f]
    (g : Y ⟶ Z) : Set.range (f ≫ g) = Set.range g := by
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr f.surjective, Set.image_univ]

end FLT.Mazur
