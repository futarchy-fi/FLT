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
after identifying the resulting Weierstrass equation. Combined coefficient
and coordinate transports obey the corresponding composition law. If the
coefficient composite is identity and the coordinate product is negation,
the cyclic composite is identity for equations with a₁ = a₃ = 0.

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

theorem cyclicCoordinateRingMap_comp (f : R →+* S) (g : S →+* T)
    (V : WeierstrassCurve S) [V.IsElliptic]
    (U : WeierstrassCurve T) [U.IsElliptic]
    (C : VariableChange S) (D : VariableChange T)
    (hC : C • W.map f = V) (hD : D • V.map g = U) :
    ((groupCyclicParameterIso p (variableChangeCongrOverIso (V.map g) U D hD)).hom.left ≫
      ringHomCyclicMap V p g) ≫
      ((groupCyclicParameterIso p (variableChangeCongrOverIso (W.map f) V C hC)).hom.left ≫
        ringHomCyclicMap W p f) =
    (groupCyclicParameterIso p (variableChangeCongrOverIso ((W.map f).map g) U
      (D * C.map g) (by rw [mul_smul, map_variableChange, hC, hD]))).hom.left ≫
        (cyclicModelCongr _ p _ (W.map_map f g)).hom.left ≫
          ringHomCyclicMap W p (g.comp f) := by
  have hc := ringHomCyclicMap_variableChange (W.map f) p g V C hC
  have ht := congrArg (fun e => e.hom.left)
    (variableChangeCyclic_trans ((W.map f).map g) p (V.map g) U D (C.map g)
      (by rw [map_variableChange, hC]) hD)
  simp only [Iso.trans_hom, Over.comp_left] at ht
  simp only [Category.assoc]
  rw [← Category.assoc (ringHomCyclicMap V p g), ← hc]
  simp only [← Category.assoc]
  rw [ht]
  simp only [Category.assoc]
  rw [ringHomCyclicMap_comp]

theorem variableChangeCyclic_source_congr
    (A B U : WeierstrassCurve R) [A.IsElliptic] [B.IsElliptic] [U.IsElliptic]
    (hAB : A = B) (C : VariableChange R) (hC : C • A = U) :
    (groupCyclicParameterIso p (variableChangeCongrOverIso A U C hC)).hom.left ≫
      (cyclicModelCongr A p B hAB).hom.left =
        (groupCyclicParameterIso p
          (variableChangeCongrOverIso B U C (hAB ▸ hC))).hom.left := by
  subst B
  simp [cyclicModelCongr]

theorem cyclicCoordinateRingMap_comp_eq (f : R →+* S) (g : S →+* T) (k : R →+* T)
    (hk : g.comp f = k)
    (V : WeierstrassCurve S) [V.IsElliptic]
    (U : WeierstrassCurve T) [U.IsElliptic]
    (C : VariableChange S) (D : VariableChange T)
    (hC : C • W.map f = V) (hD : D • V.map g = U) :
    ((groupCyclicParameterIso p (variableChangeCongrOverIso (V.map g) U D hD)).hom.left ≫
      ringHomCyclicMap V p g) ≫
      ((groupCyclicParameterIso p (variableChangeCongrOverIso (W.map f) V C hC)).hom.left ≫
        ringHomCyclicMap W p f) =
    (groupCyclicParameterIso p (variableChangeCongrOverIso ((W.map f).map g) U
      (D * C.map g) (by rw [mul_smul, map_variableChange, hC, hD]))).hom.left ≫
        (cyclicModelCongr _ p _ ((W.map_map f g).trans (congrArg W.map hk))).hom.left ≫
          ringHomCyclicMap W p k := by
  subst k
  exact cyclicCoordinateRingMap_comp W p f g V U C D hC hD

theorem cyclicCoordinateRingMap_return_neg (f : R →+* S) (g : S →+* R)
    (hgf : g.comp f = RingHom.id R)
    (V : WeierstrassCurve S) [V.IsElliptic]
    (C : VariableChange S) (D : VariableChange R)
    (hC : C • W.map f = V) (hD : D • V.map g = W)
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (hprod : D * C.map g = signCoordinateChange (-1) 0) :
    ((groupCyclicParameterIso p (variableChangeCongrOverIso (V.map g) W D hD)).hom.left ≫
      ringHomCyclicMap V p g) ≫
      ((groupCyclicParameterIso p (variableChangeCongrOverIso (W.map f) V C hC)).hom.left ≫
        ringHomCyclicMap W p f) = 𝟙 _ := by
  have ht := cyclicCoordinateRingMap_comp_eq W p f g (RingHom.id R) hgf V W C D hC hD
  simp only [ringHomCyclicMap_id, Category.comp_id] at ht
  rw [variableChangeCyclic_source_congr] at ht
  have hn : signCoordinateChange (-1 : Rˣ) 0 • W = W := by
    have h : (W.map f).map g = W := by
      rw [WeierstrassCurve.map_map, hgf]
      rfl
    rw [← hprod, mul_smul, ← h, map_variableChange, hC, hD]
    exact h.symm
  have he := variableChangeCyclic_congr W p W (D * C.map g)
    (signCoordinateChange (-1) 0) (by simpa only [WeierstrassCurve.map_id] using
      (show (D * C.map g) • W.map (RingHom.id R) = W from
        by rw [← hgf, ← WeierstrassCurve.map_map, mul_smul, map_variableChange, hC, hD]))
    hn hprod
  have hz := signCoordinateCyclic_neg_one W p ha₁ ha₃ hn
  exact ht.trans (by
    simpa only [WeierstrassCurve.map_id, Iso.refl_hom, Over.id_left] using
      congrArg (fun e : scalarQuotientModel W p ≅ scalarQuotientModel W p =>
        e.hom.left) (he.trans hz))

end WeierstrassCurve.CubicCharts
