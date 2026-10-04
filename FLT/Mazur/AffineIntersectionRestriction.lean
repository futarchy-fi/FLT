/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePullbackIntersection

/-!
# Restriction through the affine intersection comparison

The intersection ring comparison intertwines restriction from either chart
with the actual affine pullback map on global sections.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.AffinePullbackIntersection
variable {R : Type u} [CommRing R] {U V X : Scheme.{u}}
  (l : Spec (.of R) ⟶ U) (r : Spec (.of R) ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion k] (H : IsPullback l r j k)

/-- Restriction from the first chart is the first pullback map in affine coordinates. -/
lemma sectionsIso_restrict_left :
    X.presheaf.map (homOfLE (show (j ''ᵁ ⊤) ⊓ (k ''ᵁ ⊤) ≤ j ''ᵁ ⊤ from inf_le_left)).op ≫
      (sectionsIso l r j k H).hom =
        (j.appIso ⊤).hom ≫ l.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom := by
  let := inclusion_isOpenImmersion l r j k H
  simp only [sectionsIso, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
    ← Category.assoc, ← Functor.map_comp, Scheme.Hom.appIso_hom']
  simp only [Category.assoc, Scheme.Hom.map_appLE_assoc]
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, ← Category.assoc,
    Scheme.Hom.appLE_comp_appLE]
  rfl

/-- Restriction from the second chart is the second pullback map in affine coordinates. -/
lemma sectionsIso_restrict_right :
    X.presheaf.map (homOfLE (show (j ''ᵁ ⊤) ⊓ (k ''ᵁ ⊤) ≤ k ''ᵁ ⊤ from inf_le_right)).op ≫
      (sectionsIso l r j k H).hom =
        (k.appIso ⊤).hom ≫ r.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom := by
  let := inclusion_isOpenImmersion l r j k H
  simp only [sectionsIso, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
    ← Category.assoc, ← Functor.map_comp, Scheme.Hom.appIso_hom']
  simp only [Category.assoc, Scheme.Hom.map_appLE_assoc]
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, ← Category.assoc,
    Scheme.Hom.appLE_comp_appLE]
  have hi : inclusion l j = r ≫ k := H.w
  simp only [hi]
  rfl

/-- In affine coordinates the first restriction is the specified ring homomorphism. -/
lemma sectionsIso_restrict_spec {A : Type u} [CommRing A] (f : A →+* R)
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (H : IsPullback (Spec.map (CommRingCat.ofHom f)) r j k) (z : A) :
    (sectionsIso _ r j k H).hom
      (X.presheaf.map (homOfLE (show (j ''ᵁ ⊤) ⊓ (k ''ᵁ ⊤) ≤ j ''ᵁ ⊤
        from inf_le_left)).op ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (.of A)).inv z))) = f z := by
  have he := congrArg (fun m ↦ m.hom
    ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (.of A)).inv z)))
    (sectionsIso_restrict_left (Spec.map (CommRingCat.ofHom f)) r j k H)
  refine he.trans ?_
  change (Scheme.ΓSpecIso (.of R)).hom ((Spec.map (CommRingCat.ofHom f)).appTop
    ((j.appIso ⊤).hom ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (.of A)).inv z)))) = f z
  have hc {A B : CommRingCat.{u}} (e : A ≅ B) (a : B) : e.hom (e.inv a) = a :=
    congrArg (fun m ↦ m.hom a) e.inv_hom_id
  rw [hc]
  have hn := congrArg (fun m ↦ m.hom ((Scheme.ΓSpecIso (.of A)).inv z))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
  change (Scheme.ΓSpecIso (.of R)).hom ((Spec.map (CommRingCat.ofHom f)).appTop
    ((Scheme.ΓSpecIso (.of A)).inv z)) =
    f ((Scheme.ΓSpecIso (.of A)).hom ((Scheme.ΓSpecIso (.of A)).inv z)) at hn
  rwa [hc] at hn

/-- In affine coordinates the second restriction is the specified ring homomorphism. -/
lemma sectionsIso_restrict_right_spec {A : Type u} [CommRing A] (f : A →+* R)
    (k : Spec (.of A) ⟶ X) [IsOpenImmersion k]
    (H : IsPullback l (Spec.map (CommRingCat.ofHom f)) j k) (z : A) :
    (sectionsIso l _ j k H).hom
      (X.presheaf.map (homOfLE (show (j ''ᵁ ⊤) ⊓ (k ''ᵁ ⊤) ≤ k ''ᵁ ⊤
        from inf_le_right)).op ((k.appIso ⊤).inv ((Scheme.ΓSpecIso (.of A)).inv z))) = f z := by
  have he := congrArg (fun m ↦ m.hom
    ((k.appIso ⊤).inv ((Scheme.ΓSpecIso (.of A)).inv z)))
    (sectionsIso_restrict_right l (Spec.map (CommRingCat.ofHom f)) j k H)
  refine he.trans ?_
  change (Scheme.ΓSpecIso (.of R)).hom ((Spec.map (CommRingCat.ofHom f)).appTop
    ((k.appIso ⊤).hom ((k.appIso ⊤).inv ((Scheme.ΓSpecIso (.of A)).inv z)))) = f z
  have hc {A B : CommRingCat.{u}} (e : A ≅ B) (a : B) : e.hom (e.inv a) = a :=
    congrArg (fun m ↦ m.hom a) e.inv_hom_id
  rw [hc]
  have hn := congrArg (fun m ↦ m.hom ((Scheme.ΓSpecIso (.of A)).inv z))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
  change (Scheme.ΓSpecIso (.of R)).hom ((Spec.map (CommRingCat.ofHom f)).appTop
    ((Scheme.ΓSpecIso (.of A)).inv z)) =
    f ((Scheme.ΓSpecIso (.of A)).hom ((Scheme.ΓSpecIso (.of A)).inv z)) at hn
  rwa [hc] at hn

end FLT.Mazur.AffinePullbackIntersection
