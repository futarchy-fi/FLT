/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.IntegralCartierConstantPoints
public import FLT.GroupScheme.RaynaudRankThreeExtension

/-!
# Integral isomorphisms of finite-flat objects

Isomorphisms are contravariant bialgebra equivalences of the integral coordinate
rings. Their maps on the chosen geometric points are induced by scalar extension
and precomposition, so the integral and generic comparisons cannot vary independently.
Faithfulness of the generic fibre turns extensions of mutually inverse point maps
into an integral isomorphism. Over the three-adic integers the order-three extension
theorem supplies both extensions without additional hypotheses.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]

/-- An integral isomorphism of models, contravariant on coordinate bialgebras. -/
abbrev FF.Iso (X Y : FF R K) := Y.CoordinateRing ≃ₐc[R] X.CoordinateRing

/-- Extensions of inverse generic morphisms are inverse on integral coordinates. -/
theorem modelHom_comp_eq_id_of_generic_inverse [PerfectField K] [IsFractionRing R K]
    {X Y : FF R K} (f : ModelHom X Y) (g : ModelHom Y X)
    (h : ∀ x, genericHom g (genericHom f x) = x) :
    f.comp g = BialgHom.id R X.CoordinateRing := by
  apply genericHom_injective X X
  ext x
  simpa only [genericHom_comp, genericHom_id] using h x

/-- An integral morphism whose generic inverse also extends is an integral isomorphism. -/
def FF.isoOfGenericInverse [PerfectField K] [IsFractionRing R K]
    {X Y : FF R K} (f : ModelHom X Y) (g : ModelHom Y X)
    (hgf : ∀ x, genericHom g (genericHom f x) = x)
    (hfg : ∀ y, genericHom f (genericHom g y) = y) : X.Iso Y := by
  have h₁ := modelHom_comp_eq_id_of_generic_inverse f g hgf
  have h₂ := modelHom_comp_eq_id_of_generic_inverse g f hfg
  apply BialgEquiv.ofBijective f
  constructor
  · intro a b hab
    have ha := DFunLike.congr_fun h₂ a
    have hb := DFunLike.congr_fun h₂ b
    change g (f a) = a at ha
    change g (f b) = b at hb
    exact ha.symm.trans ((congrArg g hab).trans hb)
  · intro a
    exact ⟨g a, DFunLike.congr_fun h₁ a⟩

/-- The constructed equivalence retains the original integral map. -/
@[simp] theorem FF.isoOfGenericInverse_toBialgHom [PerfectField K] [IsFractionRing R K]
    {X Y : FF R K} (f : ModelHom X Y) (g : ModelHom Y X)
    (hgf : ∀ x, genericHom g (genericHom f x) = x)
    (hfg : ∀ y, genericHom f (genericHom g y) = y) :
    (FF.isoOfGenericInverse f g hgf hfg).toBialgHom = f := rfl

/-- Every equivariant additive equivalence between order-three three-adic models
extends to an integral bialgebra equivalence with the specified point comparison. -/
theorem exists_iso_of_order_three (X Y : FF ℤ_[3] ℚ_[3])
    (hX : Nat.card X.Points = 3) (e : X.Points ≃+ Y.Points)
    (he : ∀ (σ : AlgebraicClosure ℚ_[3] ≃ₐ[ℚ_[3]] AlgebraicClosure ℚ_[3]) x,
      e (σ • x) = σ • e x) :
    ∃ i : X.Iso Y, ∀ x, genericHom i.toBialgHom x = e x := by
  let f : GenericGaloisHom X Y := { toAddMonoidHom := e.toAddMonoidHom, map_smul' := he }
  let g : GenericGaloisHom Y X :=
    { toAddMonoidHom := e.symm.toAddMonoidHom
      map_smul' := fun σ y ↦ by
        apply e.injective
        change e (e.symm (σ • y)) = e (σ • e.symm y)
        rw [e.apply_symm_apply, he, e.apply_symm_apply] }
  have hY : Nat.card Y.Points = 3 := (Nat.card_congr e.toEquiv).symm.trans hX
  obtain ⟨fO, hfO, _⟩ := raynaud_extend_generic_morphism_of_order_three X Y hX f
  obtain ⟨gO, hgO, _⟩ := raynaud_extend_generic_morphism_of_order_three Y X hY g
  have hgf : ∀ x, genericHom gO (genericHom fO x) = x := by
    intro x
    rw [hfO, hgO]
    exact e.symm_apply_apply x
  have hfg : ∀ y, genericHom fO (genericHom gO y) = y := by
    intro y
    rw [hfO, hgO]
    exact e.apply_symm_apply y
  exact ⟨FF.isoOfGenericInverse fO gO hgf hfg, fun x ↦ DFunLike.congr_fun hfO x⟩

namespace FiniteFlatObject

variable {S : Type} [CommRing S] [Algebra S ℚ]

/-- An isomorphism of finite-flat objects is a bialgebra equivalence from the target's
integral coordinate ring to the source's. Its point comparison is the induced `pointMap`. -/
abbrev Iso (H J : FiniteFlatObject S) := J.model.CoordinateRing ≃ₐc[S] H.model.CoordinateRing

/-- The geometric points of an integral isomorphism are additively equivalent. -/
def Iso.pointsEquiv {H J : FiniteFlatObject S} (e : H.Iso J) : H.points ≃+ J.points :=
  AddEquiv.ofBijective (pointMap e.toBialgHom).toAddMonoidHom (pointMap_bijective e)

/-- The point equivalence is precisely the map induced by the integral coordinates. -/
@[simp] theorem Iso.pointsEquiv_apply {H J : FiniteFlatObject S} (e : H.Iso J)
    (x : H.points) : e.pointsEquiv x = pointMap e.toBialgHom x := rfl

/-- Integral isomorphisms preserve the Galois action on geometric points. -/
theorem Iso.pointsEquiv_smul {H J : FiniteFlatObject S} (e : H.Iso J)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : H.points) :
    e.pointsEquiv (σ • x) = σ • e.pointsEquiv x :=
  map_smul (pointMap e.toBialgHom) σ x

/-- The two existing model interfaces induce the same map on chosen geometric points. -/
theorem pointMap_eq_genericHom {H J : FiniteFlatObject S} (f : H.Hom J) :
    pointMap f = genericHom (X := H.toFF) (Y := J.toFF) f := rfl

/-- Integral maps of finite-flat objects are determined by their geometric point maps. -/
theorem pointMap_injective [IsFractionRing S ℚ] (H J : FiniteFlatObject S) :
    Function.Injective (pointMap (H := H) (J := J)) :=
  genericHom_injective H.toFF J.toFF

end FiniteFlatObject
end ThreeAdicPlan
