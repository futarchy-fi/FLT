/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCyclicCoefficientTower
/-! # Cyclic transport along explicit ring maps

Identity and composition of the actual coefficient maps apply to explicit
ring homomorphisms, without a fixed algebra structure on the coefficient
rings. Coordinate-change transport commutes with these maps.
The inverse of transport by a ring equivalence is transport by its inverse,
after identifying the resulting Weierstrass equation.

These results supply coefficient compatibilities for parameter-changing
Legendre maps. Naturality of the quadratic descended coordinate maps and
the resulting automorphism relations remain to be proved.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable [IsNoetherianRing R] [IsDomain R]
variable [IsNoetherianRing S] [IsDomain S] [IsNoetherianRing T] [IsDomain T]
variable (W : WeierstrassCurve R) [W.IsElliptic]
variable (p : ℕ) [Fact p.Prime] [Fact (IsUnit (p : R))]
variable [Fact (IsUnit (p : S))] [Fact (IsUnit (p : T))]

/-- Transport cyclic parameters contravariantly along an explicit coefficient map. -/
def ringHomCyclicMap (f : R →+* S) :
    (scalarQuotientModel (W.map f) p).left ⟶ (scalarQuotientModel W p).left := by
  letI : Algebra R S := f.toAlgebra
  exact coefficientScalarQuotientMorphism W S p

theorem ringHomCyclicMap_id :
    ringHomCyclicMap W p (RingHom.id R) = 𝟙 _ :=
  coefficientScalarQuotientMorphism_self W p

theorem ringHomCyclicMap_comp (f : R →+* S) (g : S →+* T) :
    ringHomCyclicMap (W.map f) p g ≫ ringHomCyclicMap W p f =
      (cyclicModelCongr _ p _ (W.map_map f g)).hom.left ≫
        ringHomCyclicMap W p (g.comp f) := by
  let : Algebra R S := f.toAlgebra
  let : Algebra S T := g.toAlgebra
  let : Algebra R T := (g.comp f).toAlgebra
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  exact coefficientScalarQuotientMorphism_tower W p

theorem ringEquivCyclicIso_ringHom (e : R ≃+* S) :
    (ringEquivCyclicIso W p e).hom = ringHomCyclicMap W p e.toRingHom :=
  ringEquivCyclicIso_hom W p e

theorem ringHomCyclicMap_toBase (f : R →+* S) :
    ringHomCyclicMap W p f ≫ (scalarQuotientModel W p).hom =
      (scalarQuotientModel (W.map f) p).hom ≫ Spec.map (CommRingCat.ofHom f) := by
  let : Algebra R S := f.toAlgebra
  exact coefficientScalarQuotientMorphism_toBase W S p

theorem ringHomCyclicMap_variableChange (f : R →+* S)
    (V : WeierstrassCurve R) [V.IsElliptic] (C : VariableChange R) (h : C • W = V) :
    (groupCyclicParameterIso p (variableChangeCongrOverIso (W.map f) (V.map f)
      (C.map f) (by rw [map_variableChange, h]))).hom.left ≫ ringHomCyclicMap W p f =
        ringHomCyclicMap V p f ≫
          (groupCyclicParameterIso p (variableChangeCongrOverIso W V C h)).hom.left := by
  let : Algebra R S := f.toAlgebra
  exact variableChangeCyclic_coefficient S W V C h p


theorem ringHomCyclicMap_comp_eq (f : R →+* S) (g : S →+* T) (k : R →+* T)
    (hk : g.comp f = k) :
    ringHomCyclicMap (W.map f) p g ≫ ringHomCyclicMap W p f =
      (cyclicModelCongr _ p _ ((W.map_map f g).trans (congrArg W.map hk))).hom.left ≫
        ringHomCyclicMap W p k := by
  subst k
  exact ringHomCyclicMap_comp W p f g

omit [IsNoetherianRing R] [IsDomain R] [IsNoetherianRing S] [IsDomain S]
    [W.IsElliptic] in
theorem ringEquiv_map_return (e : R ≃+* S) :
    (W.map e.toRingHom).map e.symm.toRingHom = W := by
  rw [WeierstrassCurve.map_map]
  have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by
    ext x
    exact e.symm_apply_apply x
  rw [he]
  rfl

theorem ringHomCyclicMap_equiv_return (e : R ≃+* S) :
    ringHomCyclicMap (W.map e.toRingHom) p e.symm.toRingHom ≫
        ringHomCyclicMap W p e.toRingHom =
      (cyclicModelCongr _ p W (ringEquiv_map_return W e)).hom.left := by
  have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by
    ext x
    exact e.symm_apply_apply x
  simpa only [ringHomCyclicMap_id, Category.comp_id, WeierstrassCurve.map_id] using
    ringHomCyclicMap_comp_eq W p e.toRingHom e.symm.toRingHom (RingHom.id R) he

theorem ringEquivCyclicIso_inv_ringHom (e : R ≃+* S) :
    (ringEquivCyclicIso W p e).inv =
      (cyclicModelCongr _ p W (ringEquiv_map_return W e)).inv.left ≫
        ringHomCyclicMap (W.map e.toRingHom) p e.symm.toRingHom := by
  apply (cancel_mono (ringEquivCyclicIso W p e).hom).mp
  rw [Iso.inv_hom_id, Category.assoc, ringEquivCyclicIso_ringHom,
    ringHomCyclicMap_equiv_return]
  exact (congrArg Over.Hom.left
    (cyclicModelCongr _ p W (ringEquiv_map_return W e)).inv_hom_id).symm

end WeierstrassCurve.CubicCharts
