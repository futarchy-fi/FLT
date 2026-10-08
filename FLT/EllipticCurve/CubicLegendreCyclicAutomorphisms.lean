/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendreDescendedBraid
/-! # Legendre cyclic automorphisms over the j-line

Coefficient equivalences transport the cyclic scheme. Combining this transport
with the descended swap and reciprocal isomorphisms gives actual automorphisms
of the Legendre cyclic scheme, preserving its projection to the j-line.

The involution and braid relations for these parameter-changing automorphisms
remain to be proved before constructing the group action or its quotient.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
variable [IsNoetherianRing R] [IsDomain R] [IsNoetherianRing S] [IsDomain S]
variable (W : WeierstrassCurve R) [W.IsElliptic]
variable (p : ℕ) [Fact p.Prime] [Fact (IsUnit (p : R))] [Fact (IsUnit (p : S))]

/-- Transport the cyclic scheme through an equivalence of coefficient rings. -/
def ringEquivCyclicIso (e : R ≃+* S) :
    (scalarQuotientModel (W.map e.toRingHom) p).left ≅ (scalarQuotientModel W p).left := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  letI : IsIso (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    show IsIso (Scheme.Spec.mapIso e.toCommRingCatIso.op).hom from inferInstance
  exact (Over.forget _).mapIso (coefficientScalarQuotientIso W S p) ≪≫
    asIso (pullback.fst (scalarQuotientModel W p).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))

theorem ringEquivCyclicIso_hom (e : R ≃+* S) :
    letI : Algebra R S := e.toRingHom.toAlgebra
    (ringEquivCyclicIso W p e).hom = coefficientScalarQuotientMorphism W S p := by
  let : Algebra R S := e.toRingHom.toAlgebra
  exact coefficientScalarQuotientComparison_fst W S p

theorem ringEquivCyclicIso_toBase (e : R ≃+* S) :
    (ringEquivCyclicIso W p e).hom ≫ (scalarQuotientModel W p).hom =
      (scalarQuotientModel (W.map e.toRingHom) p).hom ≫
        Spec.map (CommRingCat.ofHom e.toRingHom) := by
  let : Algebra R S := e.toRingHom.toAlgebra
  rw [ringEquivCyclicIso_hom]
  exact coefficientScalarQuotientMorphism_toBase W S p

/-- Identify cyclic models of equal Weierstrass equations. -/
def cyclicModelCongr (V : WeierstrassCurve R) [V.IsElliptic] (h : W = V) :
    scalarQuotientModel W p ≅ scalarQuotientModel V p := by
  subst V
  exact Iso.refl _

/-- Combine a parameter equivalence with an isomorphism of cyclic models. -/
def cyclicParameterAut (e : R ≃+* R) (V : WeierstrassCurve R) [V.IsElliptic]
    (h : W.map e.toRingHom = V) (i : scalarQuotientModel V p ≅ scalarQuotientModel W p) :
    (scalarQuotientModel W p).left ≅ (scalarQuotientModel W p).left :=
  (Over.forget _).mapIso
    (i.symm ≪≫ (cyclicModelCongr (W.map e.toRingHom) p V h).symm) ≪≫
      ringEquivCyclicIso W p e

theorem cyclicParameterAut_toBase (e : R ≃+* R) (V : WeierstrassCurve R) [V.IsElliptic]
    (h : W.map e.toRingHom = V) (i : scalarQuotientModel V p ≅ scalarQuotientModel W p) :
    (cyclicParameterAut W p e V h i).hom ≫ (scalarQuotientModel W p).hom =
      (scalarQuotientModel W p).hom ≫ Spec.map (CommRingCat.ofHom e.toRingHom) := by
  let a := i.symm ≪≫ (cyclicModelCongr (W.map e.toRingHom) p V h).symm
  change (a.hom.left ≫ (ringEquivCyclicIso W p e).hom) ≫ _ = _
  rw [Category.assoc, ringEquivCyclicIso_toBase, ← Category.assoc]
  exact congrArg (fun k => k ≫ Spec.map (CommRingCat.ofHom e.toRingHom)) a.hom.w

theorem legendreSwap_model_map (p : ℕ) :
    (legendreModel p).map (legendreSwapParameterEquiv p).toRingHom =
      legendreCurve (1 - legendreParameter p) := by
  change (legendreCurve (legendreParameter p)).map (legendreSwapParameterMap p) = _
  rw [legendreCurve_map, legendreSwapParameterMap_parameter]

theorem legendreReciprocal_model_map (p : ℕ) :
    (legendreModel p).map (legendreReciprocalParameterEquiv p).toRingHom =
      legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p) := by
  change (legendreCurve (legendreParameter p)).map (legendreReciprocalParameterMap p) = _
  rw [legendreCurve_map, legendreReciprocalParameterMap_parameter]

/-- The actual cyclic automorphism covering the parameter swap. -/
def legendreSwapCyclicAut (p : ℕ) [Fact p.Prime] :
    (scalarQuotientModel (legendreModel p) p).left ≅
      (scalarQuotientModel (legendreModel p) p).left :=
  cyclicParameterAut (legendreModel p) p (legendreSwapParameterEquiv p)
    (legendreCurve (1 - legendreParameter p)) (legendreSwap_model_map p)
    (legendreSwapDescendedIso p)

/-- The actual cyclic automorphism covering parameter inversion. -/
def legendreReciprocalCyclicAut (p : ℕ) [Fact p.Prime] :
    (scalarQuotientModel (legendreModel p) p).left ≅
      (scalarQuotientModel (legendreModel p) p).left :=
  cyclicParameterAut (legendreModel p) p (legendreReciprocalParameterEquiv p)
    (legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))
    (legendreReciprocal_model_map p) (legendreReciprocalDescendedIso p)

theorem legendreSwapCyclicAut_toBase (p : ℕ) [Fact p.Prime] :
    (legendreSwapCyclicAut p).hom ≫ (scalarQuotientModel (legendreModel p) p).hom =
      (scalarQuotientModel (legendreModel p) p).hom ≫
        Spec.map (CommRingCat.ofHom (legendreSwapParameterMap p)) :=
  cyclicParameterAut_toBase _ _ _ _ _ _

theorem legendreReciprocalCyclicAut_toBase (p : ℕ) [Fact p.Prime] :
    (legendreReciprocalCyclicAut p).hom ≫ (scalarQuotientModel (legendreModel p) p).hom =
      (scalarQuotientModel (legendreModel p) p).hom ≫
        Spec.map (CommRingCat.ofHom (legendreReciprocalParameterMap p)) :=
  cyclicParameterAut_toBase _ _ _ _ _ _

/-- The Legendre cyclic scheme with its projection to the j-line. -/
def legendreCyclicOverJ (p : ℕ) [Fact p.Prime] : Over (Spec (.of (LegendreJBase p))) :=
  Over.mk ((scalarQuotientModel (legendreModel p) p).hom ≫
    Spec.map (CommRingCat.ofHom (legendreJMap p) :
      CommRingCat.of (LegendreJBase p) ⟶ CommRingCat.of (LegendreBase p)))

theorem legendreParameterSpec_comp_j (p : ℕ) (f : LegendreBase p →+* LegendreBase p)
    (hj : f (legendreModel p).j = (legendreModel p).j) :
    Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom (legendreJMap p) :
      CommRingCat.of (LegendreJBase p) ⟶ CommRingCat.of (LegendreBase p)) =
      Spec.map (CommRingCat.ofHom (legendreJMap p) :
      CommRingCat.of (LegendreJBase p) ⟶ CommRingCat.of (LegendreBase p)) := by
  have hc : (CommRingCat.ofHom (legendreJMap p) ≫ CommRingCat.ofHom f :
      CommRingCat.of (LegendreJBase p) ⟶ CommRingCat.of (LegendreBase p)) =
      CommRingCat.ofHom (legendreJMap p) :=
    congrArg (fun g : LegendreJBase p →+* LegendreBase p =>
      (CommRingCat.ofHom g : CommRingCat.of (LegendreJBase p) ⟶
        CommRingCat.of (LegendreBase p))) (legendreParameterMap_comp_jMap p f hj)
  rw [← Spec.map_comp, hc]

/-- The swap automorphism as an isomorphism over the j-line. -/
def legendreSwapCyclicOverJ (p : ℕ) [Fact p.Prime] :
    legendreCyclicOverJ p ≅ legendreCyclicOverJ p :=
  Over.isoMk (legendreSwapCyclicAut p) (by
    change (legendreSwapCyclicAut p).hom ≫
      ((scalarQuotientModel (legendreModel p) p).hom ≫ _) = _
    rw [← Category.assoc, legendreSwapCyclicAut_toBase, Category.assoc,
      legendreParameterSpec_comp_j p _ (legendreSwapParameterMap_j p)]
    rfl)

/-- The reciprocal automorphism as an isomorphism over the j-line. -/
def legendreReciprocalCyclicOverJ (p : ℕ) [Fact p.Prime] :
    legendreCyclicOverJ p ≅ legendreCyclicOverJ p :=
  Over.isoMk (legendreReciprocalCyclicAut p) (by
    change (legendreReciprocalCyclicAut p).hom ≫
      ((scalarQuotientModel (legendreModel p) p).hom ≫ _) = _
    rw [← Category.assoc, legendreReciprocalCyclicAut_toBase, Category.assoc,
      legendreParameterSpec_comp_j p _ (legendreReciprocalParameterMap_j p)]
    rfl)

end WeierstrassCurve.CubicCharts
