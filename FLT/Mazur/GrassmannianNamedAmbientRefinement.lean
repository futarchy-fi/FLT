/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientPullbackCoherence
public import FLT.Mazur.AffineTildeMorphismCoherence

/-!
# Coefficient coherence with named composite maps

The ambient pullback comparison sends every original tensor to its coefficient
image. This normalization proves compatibility with successive refinements.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
open AffineTildePullbackSectionMap AffineIteratedPullbackSections
universe u
variable {R A B C M : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C] [AddCommGroup M] [Module R M]
variable (f : A →ₐ[R] B) (g : B →ₐ[R] C) (k : A →ₐ[R] C)
  (hk : g.comp f = k)

attribute [local irreducible] grassmannianAmbientSheafPullbackIso compositeIso
attribute [local irreducible] Scheme.Modules.pullback

include hk in
/-- Successive coefficient pullbacks agree with direct ambient pullback. -/
theorem grassmannianAmbientSheafPullbackIso_named
    (w : Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      Spec.map (CommRingCat.ofHom f.toRingHom) =
        Spec.map (CommRingCat.ofHom k.toRingHom)) :
    (compositeIso (Spec.map (CommRingCat.ofHom g.toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom k.toRingHom)) w
      (tilde (ModuleCat.of A (A ⊗[R] M)))).inv ≫
        (pullback (Spec.map (CommRingCat.ofHom g.toRingHom))).map
          (grassmannianAmbientSheafPullbackIso (M := M) f).hom ≫
        (grassmannianAmbientSheafPullbackIso (M := M) g).hom =
      (grassmannianAmbientSheafPullbackIso (M := M) k).hom := by
  exact AffineTildeMorphismCoherence.hom_comp
    (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom g.toRingHom)
    (CommRingCat.ofHom k.toRingHom) w
    (ModuleCat.of A (A ⊗[R] M)) (ModuleCat.of B (B ⊗[R] M))
    (ModuleCat.of C (C ⊗[R] M))
    _ _ _ (LinearMap.rTensor M f.toLinearMap) (LinearMap.rTensor M g.toLinearMap)
      (LinearMap.rTensor M k.toLinearMap)
      (grassmannianAmbientSheafPullbackIso_unit f)
      (grassmannianAmbientSheafPullbackIso_unit g)
      (grassmannianAmbientSheafPullbackIso_unit k)
      (fun x ↦ (grassmannianAmbientCoefficient_comp f g x).trans
        (congrArg (fun l : A →ₐ[R] C ↦ LinearMap.rTensor M l.toLinearMap x) hk))

end FLT.Mazur.GrassmannianChart
