/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPolynomialNodeEquiv
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# The full initial arithmetic node as an actual scheme open

The inverse coordinate maps identify a principal open of the original
initial scheme with a principal open of pq=s, including the node intersection.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "A" => Coordinate W s b3 b4 b6
local notation "L" => PolynomialNodeOpen W s
local notation "O" => PolynomialInitialOpen W s b3 b4 b6 r

/-- The actual inclusion of the original initial node neighborhood. -/
def polynomialInitialOpenInclusion : Spec (.of O) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A O))

instance polynomialInitialOpenInclusion_isOpenImmersion :
    IsOpenImmersion (polynomialInitialOpenInclusion W s b3 b4 b6 r) :=
  IsOpenImmersion.of_isLocalization
    (polynomialSmallFactor W s b3 b4 b6 r + algebraMap R A W.a₁)

/-- The original initial neighborhood is the constructed full smoothing-node open. -/
def polynomialNodeIso : Spec (.of L) ≅ Spec (.of O) :=
  Scheme.Spec.mapIso
    (polynomialNodeEquiv W s b3 b4 b6 r hr I hI hrI h3).toRingEquiv.toCommRingCatIso.op

/-- The actual coefficient-preserving initial node chart, including the complement of D(t). -/
def polynomialNodeChart : Spec (.of L) ⟶ Spec (.of A) :=
  (polynomialNodeIso W s b3 b4 b6 r hr I hI hrI h3).hom ≫
    polynomialInitialOpenInclusion W s b3 b4 b6 r

instance polynomialNodeChart_isOpenImmersion :
    IsOpenImmersion (polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The full node chart is induced by the independently constructed original evaluation. -/
theorem polynomialNodeChart_eq_spec :
    polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3 =
      Spec.map (CommRingCat.ofHom
        (polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact polynomialNodeForward_base W s b3 b4 b6 r hr I hI hrI h3 z

/-- The full arithmetic node chart retains the original coefficient morphism. -/
@[reassoc] theorem polynomialNodeChart_structure :
    polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3 ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)) =
        Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
  rw [polynomialNodeChart_eq_spec, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3).commutes z

end FLT.Mazur.WeierstrassModificationX
