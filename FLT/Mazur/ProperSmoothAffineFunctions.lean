/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConnectedPointedLineSheafDescent
public import FLT.Mazur.NoetherianProperAffineBaseChange

/-!
# Actual functions over arbitrary original affine bases

Finite coefficient descent produces a connected proper smooth pointed model.
The universal Noetherian comparison then recovers actual global functions over
the original ring, with no Noetherian or reducedness assumption on that ring.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ProperSmoothAffineFunctions
open Approximation FCurve

/-- Proper smooth connected pointed families have only base functions over every affine ring. -/
theorem spec_appTop_bijective {A : Type} [CommRing A] {X : Scheme.{0}}
    (p : X ⟶ Spec (.of A)) [IsProper p] [Smooth p] [GeometricallyConnected p]
    (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _) : Function.Bijective p.appTop := by
  obtain ⟨S, hS, _, Y, q, M, hq, hsm, hconn, _, t, f, ht, hf, _, _⟩ :=
    exists_connected_proper_smooth_pointed_line_sheaf_descent p s hs
      (structureModule X) structureModule_locallyFreeRankOne ∅ Set.finite_empty
  let _ : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  let _ : IsNoetherianRing Γ(Spec (.of S), ⊤) :=
    isNoetherianRing_of_ringEquiv S (affineSectionRingEquiv (.of S)).symm
  let _ := geometricallyReduced_of_smooth q
  exact NoetherianProperAffineBaseChange.appTop_bijective hf t ht

variable {X S : Scheme.{0}} [IsAffine S] (f : X ⟶ S)
  [IsProper f] [Smooth f] [GeometricallyConnected f]
  (s : S ⟶ X) (hs : s ≫ f = 𝟙 _)

include s hs in
/-- The comparison applies to an arbitrary affine scheme with its actual structure morphism. -/
theorem appTop_bijective : Function.Bijective f.appTop := by
  let _ : GeometricallyConnected (f ≫ S.isoSpec.hom) :=
    MorphismProperty.RespectsIso.postcomp _ _ _ ‹GeometricallyConnected f›
  have H := spec_appTop_bijective (f ≫ S.isoSpec.hom) (S.isoSpec.inv ≫ s) (by
    simp only [Category.assoc, ← Category.assoc s f, hs, Category.id_comp, Iso.inv_hom_id])
  have hi : IsIso (f ≫ S.isoSpec.hom).appTop :=
    (ConcreteCategory.isIso_iff_bijective _).mpr H
  rw [Scheme.Hom.comp_appTop, isIso_comp_left_iff] at hi
  exact (ConcreteCategory.isIso_iff_bijective _).mp hi

/-- Global functions are exactly the original affine base functions. -/
def sectionsIso : Γ(S, ⊤) ≅ Γ(X, ⊤) :=
  (RingEquiv.ofBijective f.appTop.hom (appTop_bijective f s hs)).toCommRingCatIso

/-- The comparison uses the actual structural pullback. -/
lemma sectionsIso_hom : (sectionsIso f s hs).hom = f.appTop := rfl

/-- The comparison inverse is evaluation at the specified section. -/
lemma sectionsIso_inv : (sectionsIso f s hs).inv = s.appTop := by
  apply (cancel_epi (sectionsIso f s hs).hom).mp
  rw [Iso.hom_inv_id, sectionsIso_hom, ← Scheme.Hom.comp_appTop, hs,
    Scheme.Hom.id_appTop]

end FLT.Mazur.ProperSmoothAffineFunctions
