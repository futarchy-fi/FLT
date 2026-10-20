/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CharacterCoefficientSeparatedExt
public import FLT.Mazur.DiagonalizableProductScheme
public import FLT.Mazur.MultiplicativeGroupObjectHom

/-!
# Injective coefficients detect character homomorphisms

On character sources and their full products, geometric base change along an
injective coefficient map detects equality into separated groups. Thus the
homomorphism law can be recovered without a faithfully flat coefficient map.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace FLT.Mazur.CharacterSchemeBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable (A B G : Type u) [CommRing A] [CommRing B] [Algebra A B] [AddCommMonoid G]
  (hAB : Function.Injective (algebraMap A B))

include hAB

/-- Pullback detects maps from the entire character scheme to a separated relative scheme. -/
theorem pullback_map_injective (Y : Over (Spec (.of A))) [IsSeparated Y.hom] :
    Function.Injective (fun f : model A G ⟶ Y => (Over.pullback (baseMap A B)).map f) := by
  intro f g he
  apply Over.OverMorphism.ext
  apply coefficientMap_separated_hom_ext A B G hAB Y.hom (f.w.trans g.w.symm)
  have h := congrArg (fun k => (overIso A B G).hom.left ≫ k.left ≫
    pullback.fst Y.hom (baseMap A B)) he
  simpa only [Over.pullback_map_left, Category.assoc, pullback.lift_fst,
    overIso_fst_assoc] using h

/-- The same detection holds on the full character product, including nilpotents. -/
theorem pullback_product_map_injective (Y : Over (Spec (.of A))) [IsSeparated Y.hom] :
    Function.Injective (fun f : model A G ⊗ model A G ⟶ Y =>
      (Over.pullback (baseMap A B)).map f) := by
  intro f g he
  apply (cancel_epi (DiagonalizableCobar.productOverIso A G).hom).mp
  apply pullback_map_injective A B (G × G) hAB Y
  simp only [Functor.map_comp, he]

/-- A recovered character morphism is a homomorphism already over its injective coefficient base. -/
theorem isMonHom_of_pullback (Y : Over (Spec (.of A))) [GrpObj Y] [IsSeparated Y.hom]
    (f : model A G ⟶ Y) [IsMonHom ((Over.pullback (baseMap A B)).map f)] : IsMonHom f := by
  apply MultiplicativeGroupObjectHom.isMonHom f
  apply pullback_product_map_injective A B G hAB Y
  apply (cancel_epi (Functor.LaxMonoidal.μ (Over.pullback (baseMap A B))
    (model A G) (model A G))).mp
  have h := IsMonHom.mul_hom ((Over.pullback (baseMap A B)).map f)
  simpa only [Functor.obj.μ_def, Category.assoc, ← Functor.map_comp,
    Functor.LaxMonoidal.μ_natural_assoc] using h

end FLT.Mazur.CharacterSchemeBaseChange
