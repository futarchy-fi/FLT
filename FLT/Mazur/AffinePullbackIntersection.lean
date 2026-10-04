/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# An affine pullback computes sections on an open intersection

This comparison allows different affine coordinates on the two sides of an
open gluing square. In particular the one-gon transition need not be an
isomorphism onto the whole torus.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.AffinePullbackIntersection
variable {R : Type u} [CommRing R] {U V X : Scheme.{u}}
  (l : Spec (.of R) ⟶ U) (r : Spec (.of R) ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion k] (H : IsPullback l r j k)

/-- The map from the affine pullback into the ambient scheme. -/
def inclusion : Spec (.of R) ⟶ X := l ≫ j

include H in
/-- The affine pullback inclusion is an open immersion. -/
lemma inclusion_isOpenImmersion : IsOpenImmersion (inclusion l j) := by
  have he : inclusion l j = H.isoPullback.hom ≫ pullback.fst j k ≫ j := by
    rw [← Category.assoc, H.isoPullback_hom_fst]
    rfl
  rw [he]
  infer_instance

/-- The affine pullback covers exactly the intersection. -/
lemma image :
    let := inclusion_isOpenImmersion l r j k H
    inclusion l j ''ᵁ ⊤ = (j ''ᵁ ⊤) ⊓ (k ''ᵁ ⊤) := by
  let := inclusion_isOpenImmersion l r j k H
  have he : inclusion l j = H.isoPullback.hom ≫ pullback.fst j k ≫ j := by
    rw [← Category.assoc, H.isoPullback_hom_fst]
    rfl
  have hs : Function.Surjective H.isoPullback.hom := H.isoPullback.hom.homeomorph.surjective
  simp only [Scheme.Hom.image_top_eq_opensRange]
  ext x
  change x ∈ Set.range (inclusion l j) ↔ x ∈ Set.range j ∩ Set.range k
  rw [he, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hs, Set.image_univ, IsOpenImmersion.range_pullback_to_base_of_left]

/-- The section ring of the actual intersection is R. -/
def sectionsIso : Γ(X, (j ''ᵁ ⊤) ⊓ (k ''ᵁ ⊤)) ≅ CommRingCat.of R :=
  let := inclusion_isOpenImmersion l r j k H
  X.presheaf.mapIso (eqToIso (image l r j k H)).op ≪≫
    (inclusion l j).appIso ⊤ ≪≫ Scheme.ΓSpecIso _

end FLT.Mazur.AffinePullbackIntersection
