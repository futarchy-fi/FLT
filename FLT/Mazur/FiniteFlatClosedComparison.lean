/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatQuotientIdealEquality

/-!
# Equal-degree closed comparisons of finite flat families

A closed immersion between finite locally free families of the same degree
is an isomorphism over an affine base. The comparison uses their actual
coordinate maps and does not discard infinitesimal structure.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.FCurve

universe u
variable {X Y S : Scheme.{u}} [IsAffine S]

set_option backward.isDefEq.respectTransparency false

/-- Affine coordinates retain the complete finite locally free degree contract. -/
theorem finiteLocallyFreeDegree_appTop (p : X ⟶ S) (d : ℕ)
    (hp : FiniteLocallyFreeDegree p d) :
    FiniteLocallyFreeDegree (Spec.map p.appTop) d := by
  let _ := hp.1
  let _ : IsAffine X := isAffine_of_isAffineHom p
  exact finiteLocallyFreeDegree_of_isPullback
    (IsPullback.of_horiz_isIso ⟨(Scheme.isoSpec_inv_naturality p).symm⟩) d hp

/-- A closed comparison between finite flat families of equal degree is an isomorphism. -/
theorem isIso_closed_of_finiteLocallyFreeDegree (p : X ⟶ S) (q : Y ⟶ S)
    (i : X ⟶ Y) [IsClosedImmersion i] (hi : i ≫ q = p) (d : ℕ)
    (hp : FiniteLocallyFreeDegree p d) (hq : FiniteLocallyFreeDegree q d) :
    IsIso i := by
  let _ := hp.1
  let _ := hq.1
  let _ : IsAffine X := isAffine_of_isAffineHom p
  let _ : IsAffine Y := isAffine_of_isAffineHom q
  let _ := p.appTop.hom.toAlgebra
  let _ := q.appTop.hom.toAlgebra
  let a : Γ(Y, ⊤) →ₐ[Γ(S, ⊤)] Γ(X, ⊤) :=
    { i.appTop.hom with
      commutes' := fun r ↦ by
        change (q.appTop ≫ i.appTop) r = p.appTop r
        rw [← Scheme.Hom.comp_appTop, hi] }
  have ha : Function.Bijective a :=
    bijective_of_surjective_of_finiteLocallyFreeDegree d
      (finiteLocallyFreeDegree_appTop q d hq) (finiteLocallyFreeDegree_appTop p d hp)
      a (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  exact IsClosedImmersion.isIso_of_injective_of_isAffine ha.1

end FLT.Mazur.FCurve
