/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.RegularPrincipalOpenLiftExt
public import FLT.Mazur.RegularCenterRatioCover

/-!
# Uniqueness over a regular principalized center

A separated contraction that is unchanged on the center-generator opens has
at most one lift from a source where the full center is regular principal.
The proof uses the actual quotient-open cover, on which each corresponding
original generator becomes regular. It is independent of the chosen regular
generator and of how the lift was constructed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.RegularCenter

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {A B : Type u} [CommRing A] [CommRing B]
  (I : Ideal A) (φ : A →+* B) (d : B) (hI : I.map φ = Ideal.span {d})
  (hd : IsRegular d) {ι : Type*} [Finite ι]
  (a : ι → A) (ha : ∀ i, a i ∈ I) (hspan : Ideal.span (Set.range a) = I)

include hI hd ha hspan in
/-- Regular principalization makes lifts unique above any such separated contraction. -/
theorem separated_lift_ext {X Y : Scheme.{u}} (c : X ⟶ Y) [IsSeparated c]
    (j : Spec (.of A) ⟶ Y)
    (e : ∀ i, Spec (.of (Localization.Away (a i))) ⟶ X)
    (he : ∀ i, IsPullback (𝟙 _) (e i) (PrincipalAffineRefinement.inclusion (a i) ≫ j) c)
    (f g : Spec (.of B) ⟶ X)
    (hf : f ≫ c = Spec.map (CommRingCat.ofHom φ) ≫ j)
    (hg : g ≫ c = Spec.map (CommRingCat.ofHom φ) ≫ j) : f = g := by
  apply (quotientCover I φ d hI hd a ha hspan).openCover.hom_ext
  intro i
  apply RegularPrincipalOpen.lift_ext c j (a i) (e i) (he i)
    (onQuotientOpen I φ d hI (a i) (ha i))
    (quotientOpen_denominator_regular I φ d hI (a i) (ha i) hd)
  · rw [Category.assoc, hf]
    change Spec.map (CommRingCat.ofHom (algebraMap B _)) ≫
      Spec.map (CommRingCat.ofHom φ) ≫ j = _
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  · rw [Category.assoc, hg]
    change Spec.map (CommRingCat.ofHom (algebraMap B _)) ≫
      Spec.map (CommRingCat.ofHom φ) ≫ j = _
    rw [← Category.assoc, ← Spec.map_comp]
    rfl

end FLT.Mazur.RegularCenter
