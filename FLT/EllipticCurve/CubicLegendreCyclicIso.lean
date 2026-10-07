/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendreCyclicDescent
/-! # Inverses of the descended Legendre cyclic maps

Invariance of the projection of a local cyclic isomorphism implies full
equivariance, using the cartesian coefficient square. Its inverse is therefore
invariant as well. Descending both maps and cancelling the effective covering
projections proves the two inverse identities.

Descent preserves identity, inverse, and composition on a fixed quadratic
cover. In particular, both previously constructed integral Legendre maps are
isomorphisms over the original coefficient base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
variable (W V : WeierstrassCurve R) [W.IsElliptic] [V.IsElliptic]
variable (p : ℕ) [Fact p.Prime] [Fact (IsUnit (p : R))]
variable (d : Rˣ) [Fact (IsUnit (2 : R))]
variable [IsNoetherianRing (QuadraticEtaleRing d)] [IsDomain (QuadraticEtaleRing d)]
variable [Fact (IsUnit (p : QuadraticEtaleRing d))]

omit [Fact (IsUnit (2 : R))] in
/-- The cyclic covering involution negates the coefficient root. -/
theorem quadraticCyclicSign_toBase :
    quadraticCyclicSign d W p ≫
      (scalarQuotientModel (W.map (algebraMap R (QuadraticEtaleRing d))) p).hom =
        (scalarQuotientModel (W.map (algebraMap R (QuadraticEtaleRing d))) p).hom ≫
          quadraticEtaleSignMorphism d := by
  rw [← coefficientCyclicEnd_quadratic, coefficientCyclicEnd_toBase]
  rfl

variable (e : scalarQuotientModel (V.map (algebraMap R (QuadraticEtaleRing d))) p ≅
  scalarQuotientModel (W.map (algebraMap R (QuadraticEtaleRing d))) p)
variable (he : quadraticCyclicSign d V p ≫
    (e.hom.left ≫ coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p) =
      e.hom.left ≫ coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p)

omit [Fact (IsUnit (2 : R))] in
include he in
/-- Invariance after projection implies full equivariance of a local cyclic isomorphism. -/
theorem quadraticCyclicIso_equivariant :
    quadraticCyclicSign d V p ≫ e.hom.left = e.hom.left ≫ quadraticCyclicSign d W p := by
  apply (coefficientScalarQuotient_isPullback W (QuadraticEtaleRing d) p).hom_ext
  · rw [Category.assoc, he, Category.assoc, quadraticCyclicSign_over]
  · rw [Category.assoc, e.hom.w, quadraticCyclicSign_toBase,
      Category.assoc, quadraticCyclicSign_toBase, ← Category.assoc, e.hom.w]

omit [Fact (IsUnit (2 : R))] in
include he in
/-- The inverse local isomorphism also has invariant projection. -/
theorem quadraticCyclicIso_inv_invariant :
    quadraticCyclicSign d W p ≫
      (e.inv.left ≫ coefficientScalarQuotientMorphism V (QuadraticEtaleRing d) p) =
        e.inv.left ≫ coefficientScalarQuotientMorphism V (QuadraticEtaleRing d) p := by
  have hid : e.hom.left ≫ e.inv.left = 𝟙 _ := by
    simpa only [Over.comp_left, Over.id_left] using congrArg Over.Hom.left e.hom_inv_id
  have hv : quadraticCyclicSign d W p ≫ e.inv.left =
      e.inv.left ≫ quadraticCyclicSign d V p := by
    apply (cancel_epi e.hom.left).mp
    rw [← Category.assoc, ← quadraticCyclicIso_equivariant W V p d e he]
    rw [Category.assoc, hid, Category.comp_id, ← Category.assoc, hid, Category.id_comp]
  rw [← Category.assoc, hv, Category.assoc, quadraticCyclicSign_over]

/-- Descend a local cyclic isomorphism and its inverse. -/
def quadraticCyclicDescIso :
    (scalarQuotientModel V p).left ≅ (scalarQuotientModel W p).left where
  hom := quadraticCyclicDesc d V p
    (e.hom.left ≫ coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p) he
  inv := quadraticCyclicDesc d W p
    (e.inv.left ≫ coefficientScalarQuotientMorphism V (QuadraticEtaleRing d) p)
    (quadraticCyclicIso_inv_invariant W V p d e he)
  hom_inv_id := by
    apply (cancel_epi (coefficientScalarQuotientMorphism V (QuadraticEtaleRing d) p)).mp
    have hid : e.hom.left ≫ e.inv.left = 𝟙 _ := by
      simpa only [Over.comp_left, Over.id_left] using congrArg Over.Hom.left e.hom_inv_id
    rw [← Category.assoc, quadraticCyclicDesc_fac, Category.assoc, quadraticCyclicDesc_fac,
      ← Category.assoc, hid, Category.id_comp, Category.comp_id]
  inv_hom_id := by
    apply (cancel_epi (coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p)).mp
    have hid : e.inv.left ≫ e.hom.left = 𝟙 _ := by
      simpa only [Over.comp_left, Over.id_left] using congrArg Over.Hom.left e.inv_hom_id
    rw [← Category.assoc, quadraticCyclicDesc_fac, Category.assoc, quadraticCyclicDesc_fac,
      ← Category.assoc, hid, Category.id_comp, Category.comp_id]



/-- The descended forward map recovers the given local isomorphism. -/
@[reassoc (attr := simp)]
theorem quadraticCyclicDescIso_hom_fac :
    coefficientScalarQuotientMorphism V (QuadraticEtaleRing d) p ≫
      (quadraticCyclicDescIso W V p d e he).hom =
        e.hom.left ≫ coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p :=
  quadraticCyclicDesc_fac d V p _ he

/-- The descended inverse recovers the inverse local isomorphism. -/
@[reassoc (attr := simp)]
theorem quadraticCyclicDescIso_inv_fac :
    coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p ≫
      (quadraticCyclicDescIso W V p d e he).inv =
        e.inv.left ≫ coefficientScalarQuotientMorphism V (QuadraticEtaleRing d) p :=
  quadraticCyclicDesc_fac d W p _
    (quadraticCyclicIso_inv_invariant W V p d e he)

/-- Descent preserves the identity isomorphism. -/
theorem quadraticCyclicDescIso_refl :
    quadraticCyclicDescIso W W p d (Iso.refl _)
      (by simpa using quadraticCyclicSign_over d W p) =
        Iso.refl (scalarQuotientModel W p).left := by
  apply Iso.ext
  apply (cancel_epi (coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p)).mp
  dsimp only [quadraticCyclicDescIso]
  rw [quadraticCyclicDesc_fac]
  simp

/-- Descent preserves inverse isomorphisms. -/
theorem quadraticCyclicDescIso_symm :
    (quadraticCyclicDescIso W V p d e he).symm =
      quadraticCyclicDescIso V W p d e.symm
        (quadraticCyclicIso_inv_invariant W V p d e he) := by
  apply Iso.ext
  rfl

variable (U : WeierstrassCurve R) [U.IsElliptic]
variable (f : scalarQuotientModel (W.map (algebraMap R (QuadraticEtaleRing d))) p ≅
  scalarQuotientModel (U.map (algebraMap R (QuadraticEtaleRing d))) p)
variable (hf : quadraticCyclicSign d W p ≫
    (f.hom.left ≫ coefficientScalarQuotientMorphism U (QuadraticEtaleRing d) p) =
      f.hom.left ≫ coefficientScalarQuotientMorphism U (QuadraticEtaleRing d) p)

omit [Fact (IsUnit (2 : R))] in
include he hf in
/-- Composition of invariant local cyclic isomorphisms is invariant. -/
theorem quadraticCyclicIso_trans_invariant :
    quadraticCyclicSign d V p ≫
      ((e ≪≫ f).hom.left ≫ coefficientScalarQuotientMorphism U (QuadraticEtaleRing d) p) =
        (e ≪≫ f).hom.left ≫ coefficientScalarQuotientMorphism U (QuadraticEtaleRing d) p := by
  simp only [Iso.trans_hom, Over.comp_left, Category.assoc]
  rw [← Category.assoc, quadraticCyclicIso_equivariant W V p d e he, Category.assoc, hf]

/-- Descent preserves composition on the same quadratic cover. -/
theorem quadraticCyclicDescIso_trans :
    (quadraticCyclicDescIso W V p d e he) ≪≫ (quadraticCyclicDescIso U W p d f hf) =
      quadraticCyclicDescIso U V p d (e ≪≫ f)
        (quadraticCyclicIso_trans_invariant W V p d e he U f hf) := by
  apply Iso.ext
  apply (cancel_epi (coefficientScalarQuotientMorphism V (QuadraticEtaleRing d) p)).mp
  dsimp only [Iso.trans_hom, quadraticCyclicDescIso]
  rw [← Category.assoc, quadraticCyclicDesc_fac, Category.assoc,
    quadraticCyclicDesc_fac, quadraticCyclicDesc_fac]
  simp only [Over.comp_left, Category.assoc]

instance quadraticCoordinateDescIsIso (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (r : R)
    (h : signCoordinateChange (quadraticEtaleUnit d) (algebraMap R (QuadraticEtaleRing d) r) •
      W.map (algebraMap R (QuadraticEtaleRing d)) = V.map (algebraMap R (QuadraticEtaleRing d))) :
    IsIso (quadraticCoordinateDesc W p d V ha₁ ha₃ r h) :=
  (quadraticCyclicDescIso W V p d
    (groupCyclicParameterIso p (variableChangeCongrOverIso
      (W.map (algebraMap R (QuadraticEtaleRing d))) (V.map (algebraMap R (QuadraticEtaleRing d)))
      (signCoordinateChange (quadraticEtaleUnit d) (algebraMap R (QuadraticEtaleRing d) r)) h))
    (quadraticCoordinateMap_invariant W p d V ha₁ ha₃ r h)).isIso_hom

instance quadraticCoordinateDescOverIsIso (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (r : R)
    (h : signCoordinateChange (quadraticEtaleUnit d) (algebraMap R (QuadraticEtaleRing d) r) •
      W.map (algebraMap R (QuadraticEtaleRing d)) = V.map (algebraMap R (QuadraticEtaleRing d))) :
    IsIso (quadraticCoordinateDescOver W p d V ha₁ ha₃ r h) := by
  have : IsIso ((Over.forget _).map (quadraticCoordinateDescOver W p d V ha₁ ha₃ r h)) :=
    quadraticCoordinateDescIsIso W V p d ha₁ ha₃ r h
  exact isIso_of_reflects_iso (quadraticCoordinateDescOver W p d V ha₁ ha₃ r h) (Over.forget _)

instance legendreSwapDescendedOverIsIso (p : ℕ) [Fact p.Prime] :
    IsIso (legendreSwapDescendedOver p) :=
  quadraticCoordinateDescOverIsIso (legendreModel p)
    (legendreCurve (1 - legendreParameter p)) p (-1 : (LegendreBase p)ˣ)
    rfl rfl 1 (legendreSwap_coordinate_equation p)

instance legendreReciprocalDescendedOverIsIso (p : ℕ) [Fact p.Prime] :
    IsIso (legendreReciprocalDescendedOver p) :=
  quadraticCoordinateDescOverIsIso (legendreModel p)
    (legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))
    p (legendreParameterUnit p) rfl rfl 0 (legendreReciprocal_coordinate_equation p)

/-- The integral cyclic swap isomorphism on the universal Legendre base. -/
def legendreSwapDescendedIso (p : ℕ) [Fact p.Prime] :
    scalarQuotientModel (legendreCurve (1 - legendreParameter p)) p ≅
      scalarQuotientModel (legendreModel p) p :=
  asIso (legendreSwapDescendedOver p)

/-- The integral cyclic reciprocal isomorphism on the universal Legendre base. -/
def legendreReciprocalDescendedIso (p : ℕ) [Fact p.Prime] :
    scalarQuotientModel
      (legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)) p ≅
        scalarQuotientModel (legendreModel p) p :=
  asIso (legendreReciprocalDescendedOver p)

/-- The swap isomorphism has the already constructed descended forward map. -/
theorem legendreSwapDescendedIso_hom (p : ℕ) [Fact p.Prime] :
    (legendreSwapDescendedIso p).hom = legendreSwapDescendedOver p := rfl

/-- The reciprocal isomorphism has the already constructed descended forward map. -/
theorem legendreReciprocalDescendedIso_hom (p : ℕ) [Fact p.Prime] :
    (legendreReciprocalDescendedIso p).hom = legendreReciprocalDescendedOver p := rfl

end WeierstrassCurve.CubicCharts
