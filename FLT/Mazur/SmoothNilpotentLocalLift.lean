/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSmoothNilpotentLift
public import FLT.Mazur.NilpotentClosedRestriction

/-!
# Local existence of whole smooth lifts

Around every point of a nilpotent thickening we construct affine neighborhoods
in the source, smooth target, and coefficient scheme. The affine lifting theorem
then gives a scheme morphism on that neighborhood, retaining the given square.
No local-ring assumption is made; agreement of these local lifts is separate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SmoothNilpotentLocalLift
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T₀ T Y Z : Scheme} (i : T₀ ⟶ T) [IsClosedImmersion i]
  (hi : IsNilpotent i.ker) (g : Y ⟶ Z) [Smooth g]
  (a : T₀ ⟶ Y) (v : T ⟶ Z) (ha : i ≫ v = a ≫ g)

include hi ha in
/-- Every point admits an actual affine neighborhood carrying a lift of the whole arrow. -/
theorem exists_lift (x : T) : ∃ W : T.Opens, IsAffineOpen W ∧ x ∈ W ∧
    ∃ b : W.toScheme ⟶ Y, (i ∣_ W) ≫ b = (i ⁻¹ᵁ W).ι ≫ a ∧ b ≫ g = W.ι ≫ v := by
  obtain ⟨x₀, rfl⟩ := NilpotentClosedRestriction.surjective i hi x
  have hx : v (i x₀) = g (a x₀) := congrArg (fun f : T₀ ⟶ Z ↦ f x₀) ha
  obtain ⟨_, ⟨(U : Z.Opens), hU, rfl⟩, hxU, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (g (a x₀))) isOpen_univ
  obtain ⟨_, ⟨(V : Y.Opens), hV, rfl⟩, hxV, hVU : V ≤ g ⁻¹ᵁ U⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hxU (g ⁻¹ᵁ U).isOpen
  let e := NilpotentClosedRestriction.homeomorph i hi
  let W₀ : T.Opens := ⟨i '' (a ⁻¹ᵁ V : Set T₀), e.isOpenMap _ (a ⁻¹ᵁ V).isOpen⟩
  have hxW : i x₀ ∈ W₀ ⊓ v ⁻¹ᵁ U := ⟨⟨x₀, hxV, rfl⟩, show v (i x₀) ∈ U from hx.symm ▸ hxU⟩
  obtain ⟨_, ⟨(W : T.Opens), hW, rfl⟩, hxW, hWW : W ≤ W₀ ⊓ v ⁻¹ᵁ U⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open hxW (W₀ ⊓ v ⁻¹ᵁ U).isOpen
  have hWV : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ V := by
    intro z hz
    obtain ⟨z', hz', he⟩ := (hWW hz).1
    exact i.isClosedEmbedding.injective he ▸ hz'
  let _ : IsAffine U.toScheme := hU
  let _ : IsAffine V.toScheme := hV
  let _ : IsAffine W.toScheme := hW
  let _ : IsAffine (i ⁻¹ᵁ W).toScheme := isAffine_of_isAffineHom (i ∣_ W)
  let g₀ := g.resLE U V hVU
  let a₀ := a.resLE V (i ⁻¹ᵁ W) hWV
  let v₀ := v.resLE U W (hWW.trans inf_le_right)
  have hg₀ : Smooth g₀ := IsZariskiLocalAtSource.resLE _ inferInstance
  have hs : (i ∣_ W) ≫ v₀ = a₀ ≫ g₀ := by
    apply (cancel_mono U.ι).mp
    dsimp only [g₀, a₀, v₀]
    rw [Category.assoc, Category.assoc, Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.resLE_comp_ι, ← Category.assoc, morphismRestrict_ι,
      Category.assoc, ha, ← Category.assoc, ← Scheme.Hom.resLE_comp_ι a hWV]
    rfl
  obtain ⟨b, hb⟩ := AffineSmoothNilpotentLift.exists_lift (i ∣_ W)
    (NilpotentClosedRestriction.restrict_nilpotent i hi W) g₀ a₀ v₀ hs
  refine ⟨W, hW, hxW, b ≫ V.ι, ?_, ?_⟩
  · rw [← Category.assoc, hb.1]
    exact Scheme.Hom.resLE_comp_ι _ _
  · rw [Category.assoc, ← Scheme.Hom.resLE_comp_ι g hVU, ← Category.assoc, hb.2]
    exact Scheme.Hom.resLE_comp_ι _ _

end FLT.Mazur.SmoothNilpotentLocalLift
