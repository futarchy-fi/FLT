/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicTorusPullback
public import FLT.Mazur.AffineRestrictionImmersion

/-!
# The cubic morphism is an immersion on each torus open

The actual surjective section pullback and the affineness of both charts give
closed immersion into the interior target chart, hence immersion into the
whole projective space.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open PolygonPinching ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ) (i : Fin n)

/-- On every torus open the actual global cubic morphism is an immersion. -/
lemma torus_isImmersion :
    IsImmersion ((torusOpen K n hn p q h i).ι ≫ cubicProjectiveMorphism K n hn p q h a) := by
  have := torus_isOpenImmersion K n hn p q h i
  let j := (torusToComponent K ≫ componentι K n i ≫ p).left
  have : IsOpenImmersion j := torus_isOpenImmersion K n hn p q h i
  have : IsAffine (MultiplicativeGroupScheme.gm K).left :=
    inferInstanceAs (IsAffine (Spec (.of (LaurentPolynomial K))))
  have hU : IsAffineOpen (j ''ᵁ ⊤) :=
    (isAffineOpen_top _).image_of_isOpenImmersion j
  have : IsAffine (j ''ᵁ ⊤).toScheme := hU
  have : IsAffine (chart K (Fin (n * 3 + 1 + 1)) (interiorIndex.{0} n)).toScheme :=
    IsAffine.of_isIso (chartIso K _ (interiorIndex.{0} n)).hom
  have hh := AffineRestrictionImmersion.immersion
    (cubicProjectiveMorphism K n hn p q h a) (j ''ᵁ ⊤)
    (chart K (Fin (n * 3 + 1 + 1)) (interiorIndex.{0} n))
    (torus_image_le_projective_preimage K n hn p q h a i)
    (torus_projective_appLE_surjective K n hn p q h a i)
  have he : j ''ᵁ ⊤ = torusOpen K n hn p q h i := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    rfl
  rwa [he] at hh

end FLT.Mazur.PolygonCubicSections
