/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianNamedAmbientRefinement
public import FLT.Mazur.SheafPullbackAmbientSectionMatch

/-!
# Sealed original ambient coefficient composition

Package the proved original-section law before specialization to a base
coefficient ring. The package is consumed by geometric ambient normalization.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A B C M : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C] [AddCommGroup M] [Module R M]
attribute [local irreducible] Scheme.Modules.pullback grassmannianAmbientSheafPullbackIso
attribute [local irreducible] AffineIteratedPullbackSections.compositeIso

/-- Equal named coefficient paths satisfy the sealed original ambient composition law. -/
theorem grassmannianAmbientComposes (f : A →ₐ[R] B) (g : B →ₐ[R] C) (k : A →ₐ[R] C)
    (hk : g.comp f = k) (w : Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      Spec.map (CommRingCat.ofHom f.toRingHom) = Spec.map (CommRingCat.ofHom k.toRingHom)) :
    SheafPullbackAmbientSectionMatch.Composes
      (Spec.map (CommRingCat.ofHom g.toRingHom)) (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom k.toRingHom)) w (tilde (ModuleCat.of A (A ⊗[R] M)))
      (grassmannianAmbientSheafPullbackIso (M := M) f)
      (grassmannianAmbientSheafPullbackIso (M := M) g)
      (grassmannianAmbientSheafPullbackIso (M := M) k) := by
  unfold SheafPullbackAmbientSectionMatch.Composes
  exact grassmannianAmbientSheafPullbackIso_named (M := M) f g k hk w

/-- Every coefficient map respects the same original base ambient composition. -/
theorem grassmannianBaseAmbientComposes (f : A →ₐ[R] B)
    (w : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.algebraMap R A =
      Spec.algebraMap R B) :
    SheafPullbackAmbientSectionMatch.Composes
      (Spec.map (CommRingCat.ofHom f.toRingHom)) (Spec.algebraMap R A)
      (Spec.algebraMap R B) w (tilde (ModuleCat.of R (R ⊗[R] M)))
      (grassmannianAmbientSheafPullbackIso (M := M) (Algebra.ofId R A))
      (grassmannianAmbientSheafPullbackIso (M := M) f)
      (grassmannianAmbientSheafPullbackIso (M := M) (Algebra.ofId R B)) :=
  grassmannianAmbientComposes (M := M) (Algebra.ofId R A) f (Algebra.ofId R B)
    (by ext) w

end FLT.Mazur.GrassmannianChart
