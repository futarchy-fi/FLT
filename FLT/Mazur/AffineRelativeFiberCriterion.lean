/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelativeFiberNeighborhood

/-!
# Affine chart fibers give finiteness over a base neighborhood

If the inverse images of affine target charts are affine on a chosen base
fiber, the actual induced fiber morphism is affine. Properness makes it
finite, and that finiteness spreads over the base.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u v

namespace FLT.Mazur.RelativeFiber

variable {X Y S : Scheme.{u}} [IsAffine S] (f : X ⟶ Y) (g : Y ⟶ S) (s : S)
  {ι : Type v} (U : ι → Y.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (hcover : ⨆ i, U i = ⊤)
  (hf : ∀ i, IsAffineOpen ((f ≫ g).fiberι s ⁻¹ᵁ (f ⁻¹ᵁ U i)))

include hU hcover hf

/-- Affine inverse-image charts on a base fiber make the actual fiber morphism affine. -/
theorem map_isAffineHom : IsAffineHom (map f g s) := by
  let _ : IsAffineHom (S.fromSpecResidueField s) := isAffineHom_of_isAffine _
  let _ : IsAffineHom (g.fiberι s) := by
    dsimp [Scheme.Hom.fiberι]
    exact MorphismProperty.pullback_fst g (S.fromSpecResidueField s)
      (inferInstance : IsAffineHom (S.fromSpecResidueField s))
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro y
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    (show g.fiberι s y ∈ ⨆ i, U i by rw [hcover]; trivial)
  refine ⟨g.fiberι s ⁻¹ᵁ U i, hi, (hU i).preimage _, ?_⟩
  rw [← Scheme.Hom.comp_preimage, map_ι, Scheme.Hom.comp_preimage]
  exact hf i

/-- Affine charts on a fiber of a proper family give a finite induced morphism. -/
theorem map_isFinite [IsProper (f ≫ g)] [IsSeparated g] : IsFinite (map f g s) := by
  let _ : IsProper f := IsProper.of_comp f g
  let _ := map_isAffineHom f g s U hU hcover hf
  exact IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩

/-- Affine chart inverse images on one fiber suffice for finiteness near that base point. -/
theorem exists_finite_neighborhood_of_affine_charts [IsProper (f ≫ g)] [IsSeparated g] :
    ∃ V : S.Opens, s ∈ V ∧ IsFinite (f ∣_ (g ⁻¹ᵁ V)) := by
  let _ := map_isFinite f g s U hU hcover hf
  exact exists_finite_neighborhood f g s

end FLT.Mazur.RelativeFiber
