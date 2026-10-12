/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientPullbackCoherence
public import FLT.Mazur.GrassmannianQuotientSheafTransition

/-!
# Natural comparison for successive affine refinements

The comparison of iterated and direct scheme pullback is a sealed natural
isomorphism. Naturality applies to every original sheaf morphism, including
the full Grassmannian quotient projection, without expanding pullback internals.
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

/-- The natural comparison of iterated and direct coefficient pullback. -/
@[irreducible] def grassmannianRefinementNatIso :
    pullback (Spec.map (CommRingCat.ofHom f.toRingHom)) ⋙
      pullback (Spec.map (CommRingCat.ofHom g.toRingHom)) ≅
        pullback (Spec.map (CommRingCat.ofHom (g.comp f).toRingHom)) :=
  pullbackComp (Spec.map (CommRingCat.ofHom g.toRingHom))
    (Spec.map (CommRingCat.ofHom f.toRingHom)) ≪≫
      pullbackCongr (AffineTripleOverlapMaps.spec_comp
        f.toRingHom g.toRingHom (g.comp f).toRingHom rfl)

/-- The canonical comparison between iterated and direct coefficient pullback. -/
def grassmannianRefinementIso (F : (Spec (.of A)).Modules) :
    (pullback (Spec.map (CommRingCat.ofHom g.toRingHom))).obj
      ((pullback (Spec.map (CommRingCat.ofHom f.toRingHom))).obj F) ≅
        (pullback (Spec.map (CommRingCat.ofHom (g.comp f).toRingHom))).obj F :=
  (grassmannianRefinementNatIso f g).app F

attribute [local irreducible] grassmannianAmbientSheafPullbackIso Scheme.Modules.pullback
attribute [local irreducible] grassmannianQuotientSheaf

/-- The canonical refinement comparison is natural in the original module sheaf. -/
@[reassoc] theorem grassmannianRefinementIso_naturality
    {F G : (Spec (.of A)).Modules} (q : F ⟶ G) :
    (pullback (Spec.map (CommRingCat.ofHom g.toRingHom))).map
        ((pullback (Spec.map (CommRingCat.ofHom f.toRingHom))).map q) ≫
      (grassmannianRefinementIso f g G).hom =
        (grassmannianRefinementIso f g F).hom ≫
          (pullback (Spec.map (CommRingCat.ofHom (g.comp f).toRingHom))).map q := by
  exact (grassmannianRefinementNatIso f g).hom.naturality q


end FLT.Mazur.GrassmannianChart
