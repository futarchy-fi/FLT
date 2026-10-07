/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCyclicCoefficientAction
public import FLT.EllipticCurve.CubicQuadraticReciprocal

/-! # Cyclic comparison across coefficient algebras

Cartesian coefficient squares transport cyclic parameters contravariantly
along algebra homomorphisms. Identity and composition hold, so algebra
isomorphisms give actual cyclic-scheme isomorphisms. For reciprocal quadratic
covers this comparison intertwines the covering signs and preserves descent
of every invariant map. Naturality of the specific Legendre coordinate
transports across the comparison is a separate remaining obligation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R]
private theorem cyclicCompare_base {S T : Type u} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)) =
        Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact f.commutes x
private theorem cyclicCompare_spec_comp {S T A : Type u}
    [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra R T] [Algebra R A] (f : T →ₐ[R] A) (g : S →ₐ[R] T) :
    Spec.map (CommRingCat.ofHom (f.comp g).toRingHom) =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom g.toRingHom) :=
  Spec.map_comp (CommRingCat.ofHom g.toRingHom) (CommRingCat.ofHom f.toRingHom)

variable [IsNoetherianRing R] [IsDomain R]
variable (W : WeierstrassCurve R) [W.IsElliptic]
variable {S T A : Type u} [CommRing S] [CommRing T] [CommRing A]
variable [Algebra R S] [Algebra R T] [Algebra R A]
variable [IsNoetherianRing S] [IsDomain S] [IsNoetherianRing T] [IsDomain T]
variable [IsNoetherianRing A] [IsDomain A]
variable (p : ℕ) [Fact p.Prime] [Fact (IsUnit (p : R))]
variable [Fact (IsUnit (p : S))] [Fact (IsUnit (p : T))] [Fact (IsUnit (p : A))]

/-- The cyclic-parameter map induced by a homomorphism of coefficient algebras. -/
def coefficientCyclicMap (f : S →ₐ[R] T) :
    (scalarQuotientModel (W.map (algebraMap R T)) p).left ⟶
      (scalarQuotientModel (W.map (algebraMap R S)) p).left :=
  (coefficientScalarQuotient_isPullback W S p).lift
    (coefficientScalarQuotientMorphism W T p)
    ((scalarQuotientModel (W.map (algebraMap R T)) p).hom ≫ Spec.map
      (CommRingCat.ofHom f.toRingHom))
    (by rw [Category.assoc, cyclicCompare_base, coefficientScalarQuotientMorphism_toBase])

/-- The comparison preserves projection to the original cyclic scheme. -/
@[reassoc (attr := simp)]
theorem coefficientCyclicMap_coefficient (f : S →ₐ[R] T) :
    coefficientCyclicMap W p f ≫ coefficientScalarQuotientMorphism W S p =
      coefficientScalarQuotientMorphism W T p :=
  (coefficientScalarQuotient_isPullback W S p).lift_fst _ _ _

/-- The comparison lies over the induced map of coefficient spectra. -/
@[reassoc (attr := simp)]
theorem coefficientCyclicMap_toBase (f : S →ₐ[R] T) :
    coefficientCyclicMap W p f ≫ (scalarQuotientModel (W.map (algebraMap R S)) p).hom =
      (scalarQuotientModel (W.map (algebraMap R T)) p).hom ≫
        Spec.map (CommRingCat.ofHom f.toRingHom) :=
  (coefficientScalarQuotient_isPullback W S p).lift_snd _ _ _

/-- The identity coefficient map induces the identity cyclic map. -/
theorem coefficientCyclicMap_id :
    coefficientCyclicMap W p (AlgHom.id R S) = 𝟙 _ := by
  apply (coefficientScalarQuotient_isPullback W S p).hom_ext
  · simp
  · rw [coefficientCyclicMap_toBase]
    simp

/-- Cyclic comparison is contravariant in coefficient algebra maps. -/
theorem coefficientCyclicMap_comp (f : S →ₐ[R] T) (g : T →ₐ[R] A) :
    coefficientCyclicMap W p g ≫ coefficientCyclicMap W p f =
      coefficientCyclicMap W p (g.comp f) := by
  apply (coefficientScalarQuotient_isPullback W S p).hom_ext
  · simp
  · rw [Category.assoc, coefficientCyclicMap_toBase, ← Category.assoc,
      coefficientCyclicMap_toBase, Category.assoc, coefficientCyclicMap_toBase,
      cyclicCompare_spec_comp]

/-- A coefficient algebra equivalence induces a cyclic-scheme isomorphism. -/
def coefficientCyclicCompareIso (e : S ≃ₐ[R] T) :
    (scalarQuotientModel (W.map (algebraMap R T)) p).left ≅
      (scalarQuotientModel (W.map (algebraMap R S)) p).left where
  hom := coefficientCyclicMap W p e.toAlgHom
  inv := coefficientCyclicMap W p e.symm.toAlgHom
  hom_inv_id := by
    rw [coefficientCyclicMap_comp]
    simpa using (coefficientCyclicMap_id W (S := T) p)
  inv_hom_id := by
    rw [coefficientCyclicMap_comp]
    simpa using (coefficientCyclicMap_id W (S := S) p)

/-- For an endomorphism, comparison agrees with the existing coefficient action. -/
theorem coefficientCyclicMap_end (f : S →ₐ[R] S) :
    coefficientCyclicMap W p f = coefficientCyclicEnd W S f p := by
  apply (coefficientScalarQuotient_isPullback W S p).hom_ext
  · rw [coefficientCyclicMap_coefficient, coefficientCyclicEnd_coefficient]
  · rw [coefficientCyclicMap_toBase, coefficientCyclicEnd_toBase]

section Reciprocal
variable (d : Rˣ) [Fact (IsUnit (2 : R))]
variable [IsNoetherianRing (QuadraticEtaleRing d)] [IsDomain (QuadraticEtaleRing d)]
variable [Fact (IsUnit (p : QuadraticEtaleRing d))]
local instance : IsNoetherianRing (QuadraticEtaleRing d⁻¹) :=
  quadraticReciprocal_isNoetherian d
local instance : IsDomain (QuadraticEtaleRing d⁻¹) :=
  quadraticReciprocal_isDomain d
local instance : Fact (IsUnit (p : QuadraticEtaleRing d⁻¹)) :=
  ⟨by simpa only [map_natCast] using
    (Fact.out : IsUnit (p : QuadraticEtaleRing d)).map (quadraticReciprocalHom d)⟩

/-- The actual cyclic schemes over reciprocal root covers are isomorphic. -/
def quadraticReciprocalCyclicIso :
    (scalarQuotientModel (W.map (algebraMap R (QuadraticEtaleRing d⁻¹))) p).left ≅
      (scalarQuotientModel (W.map (algebraMap R (QuadraticEtaleRing d))) p).left :=
  coefficientCyclicCompareIso W p (quadraticReciprocalEquiv d)

/-- Reciprocal comparison preserves the original cyclic parameter. -/
theorem quadraticReciprocalCyclicIso_coefficient :
    (quadraticReciprocalCyclicIso W p d).hom ≫
      coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p =
        coefficientScalarQuotientMorphism W (QuadraticEtaleRing d⁻¹) p :=
  coefficientCyclicMap_coefficient W p (quadraticReciprocalHom d)

/-- Reciprocal cyclic comparison intertwines the covering involutions. -/
theorem quadraticReciprocalCyclicIso_sign :
    quadraticCyclicSign d⁻¹ W p ≫ (quadraticReciprocalCyclicIso W p d).hom =
      (quadraticReciprocalCyclicIso W p d).hom ≫ quadraticCyclicSign d W p := by
  rw [← coefficientCyclicEnd_quadratic, ← coefficientCyclicEnd_quadratic,
    ← coefficientCyclicMap_end, ← coefficientCyclicMap_end]
  change coefficientCyclicMap W p (quadraticEtaleNeg d⁻¹) ≫
      coefficientCyclicMap W p (quadraticReciprocalHom d) =
    coefficientCyclicMap W p (quadraticReciprocalHom d) ≫
      coefficientCyclicMap W p (quadraticEtaleNeg d)
  rw [coefficientCyclicMap_comp, coefficientCyclicMap_comp, quadraticReciprocalHom_sign]

variable {Y : Scheme.{u}}
variable (f : (scalarQuotientModel (W.map (algebraMap R (QuadraticEtaleRing d))) p).left ⟶ Y)
variable (hf : quadraticCyclicSign d W p ≫ f = f)

include hf in
/-- An invariant map remains invariant on the reciprocal cover. -/
theorem quadraticReciprocalCyclic_invariant :
    quadraticCyclicSign d⁻¹ W p ≫ ((quadraticReciprocalCyclicIso W p d).hom ≫ f) =
      (quadraticReciprocalCyclicIso W p d).hom ≫ f := by
  rw [← Category.assoc, quadraticReciprocalCyclicIso_sign, Category.assoc, hf]

/-- Changing to the reciprocal root cover preserves the descended map. -/
theorem quadraticReciprocalCyclic_desc :
    quadraticCyclicDesc d W p f hf =
      quadraticCyclicDesc d⁻¹ W p ((quadraticReciprocalCyclicIso W p d).hom ≫ f)
        (quadraticReciprocalCyclic_invariant W p d f hf) := by
  apply (cancel_epi (coefficientScalarQuotientMorphism W (QuadraticEtaleRing d⁻¹) p)).mp
  rw [quadraticCyclicDesc_fac, ← quadraticReciprocalCyclicIso_coefficient W p d,
    Category.assoc, quadraticCyclicDesc_fac]
end Reciprocal

end WeierstrassCurve.CubicCharts
