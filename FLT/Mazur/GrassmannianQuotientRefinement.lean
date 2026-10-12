/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSheafRefinementComparison
public import FLT.Mazur.QuotientRefinementCoherence

/-!
# Refinement of original Grassmannian quotient projections

Successive affine refinements preserve the normalized ambient quotient map.
The comparison uses the actual composition isomorphism for scheme pullback.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
open AffineIteratedPullbackSections
universe u
variable {R A B C M : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C] [AddCommGroup M] [Module R M] {d : ℕ}
variable (f : A →ₐ[R] B) (g : B →ₐ[R] C)

attribute [local irreducible] Scheme.Modules.pullback pullbackComp pullbackCongr

/-- The sealed comparison is the original scheme-pullback composition comparison. -/
theorem grassmannianRefinementIso_eq_composite (F : (Spec (.of A)).Modules) :
    grassmannianRefinementIso f g F =
      comparison f.toRingHom g.toRingHom (g.comp f).toRingHom rfl F := by
  unfold grassmannianRefinementIso grassmannianRefinementNatIso
  exact NatIso.trans_app _ _ F

attribute [local irreducible] grassmannianAmbientSheafPullbackIso
attribute [local irreducible] grassmannianQuotientSheaf

/-- Inverse ambient comparisons compose with the canonical refinement comparison. -/
theorem grassmannianAmbientSheafPullbackIso_inv_comp :
    (grassmannianAmbientSheafPullbackIso (M := M) g).inv ≫
      (pullback (Spec.map (CommRingCat.ofHom g.toRingHom))).map
        (grassmannianAmbientSheafPullbackIso (M := M) f).inv ≫
      (grassmannianRefinementIso f g (tilde (ModuleCat.of A (A ⊗[R] M)))).hom =
        (grassmannianAmbientSheafPullbackIso (M := M) (g.comp f)).inv := by
  apply QuotientRefinementCoherence.inverse_triple
    (grassmannianRefinementIso f g (tilde (ModuleCat.of A (A ⊗[R] M)))).symm
    ((pullback (Spec.map (CommRingCat.ofHom g.toRingHom))).mapIso
      (grassmannianAmbientSheafPullbackIso (M := M) f))
    (grassmannianAmbientSheafPullbackIso (M := M) g)
    (grassmannianAmbientSheafPullbackIso (M := M) (g.comp f))
  rw [grassmannianRefinementIso_eq_composite]
  exact grassmannianAmbientSheafPullbackIso_comp f g _

private theorem normalizedProjection {V W : Type*} [Category V] [Category W]
    (F : V ⥤ W) {A B Q : V} {C D Q' : W}
    (a : B ⟶ A) (q : A ⟶ Q) (b : C ⟶ F.obj B)
    (c : F.obj A ⟶ D) (e : F.obj Q ⟶ Q') (a' : C ⟶ D) (q' : D ⟶ Q')
    (hn : F.map q ≫ e = c ≫ q') (hc : b ≫ F.map a ≫ c = a') :
    b ≫ F.map (a ≫ q) ≫ e = a' ≫ q' := by
  rw [Functor.map_comp, Category.assoc, hn]
  simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ q') hc

variable (N : Module.Grassmannian A (A ⊗[R] M) d)

/-- The refined original projection agrees with the direct coefficient projection. -/
@[reassoc] theorem grassmannianRefinedQuotientMap_refine :
    (grassmannianAmbientSheafPullbackIso (M := M) g).inv ≫
      (pullback (Spec.map (CommRingCat.ofHom g.toRingHom))).map
        (grassmannianRefinedQuotientMap f N) ≫
      (grassmannianRefinementIso f g (grassmannianQuotientSheaf N)).hom =
        grassmannianRefinedQuotientMap (g.comp f) N := by
  exact normalizedProjection
    (pullback (Spec.map (CommRingCat.ofHom g.toRingHom)))
    (grassmannianAmbientSheafPullbackIso (M := M) f).inv
    ((pullback (Spec.map (CommRingCat.ofHom f.toRingHom))).map
      (grassmannianQuotientSheafMap N))
    (grassmannianAmbientSheafPullbackIso (M := M) g).inv
    (grassmannianRefinementIso f g (tilde (ModuleCat.of A (A ⊗[R] M)))).hom
    (grassmannianRefinementIso f g (grassmannianQuotientSheaf N)).hom
    (grassmannianAmbientSheafPullbackIso (M := M) (g.comp f)).inv
    ((pullback (Spec.map (CommRingCat.ofHom (g.comp f).toRingHom))).map
      (grassmannianQuotientSheafMap N))
    (grassmannianRefinementIso_naturality f g (grassmannianQuotientSheafMap N))
    (grassmannianAmbientSheafPullbackIso_inv_comp f g)

end FLT.Mazur.GrassmannianChart
