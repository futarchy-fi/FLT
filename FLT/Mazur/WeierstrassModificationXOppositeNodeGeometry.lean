/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXOppositeNodeEquiv
public import FLT.Mazur.WeierstrassModificationXPolynomialNodeGeometry

/-!
# A scheme cover by the full arithmetic initial nodes

Both explicit node isomorphisms give open immersions into the original
initial scheme. Their images jointly cover the entire scheme.
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
local notation "O'" => PolynomialOppositeInitialOpen W s b3 b4 b6 r

/-- The actual inclusion of the opposite original node neighborhood. -/
def polynomialOppositeInitialInclusion : Spec (.of O') ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A O'))

instance polynomialOppositeInitialInclusion_isOpenImmersion :
    IsOpenImmersion (polynomialOppositeInitialInclusion W s b3 b4 b6 r) :=
  IsOpenImmersion.of_isLocalization (polynomialOppositeDenominator W s b3 b4 b6 r)

/-- The opposite original neighborhood is the constructed full smoothing-node open. -/
def polynomialOppositeNodeIso : Spec (.of L) ≅ Spec (.of O') :=
  Scheme.Spec.mapIso
    (polynomialOppositeNodeEquiv W s b3 b4 b6 r hr I hI hrI h3).toRingEquiv.toCommRingCatIso.op

/-- The opposite full arithmetic node chart, including the complement of D(t). -/
def polynomialOppositeNodeChart : Spec (.of L) ⟶ Spec (.of A) :=
  (polynomialOppositeNodeIso W s b3 b4 b6 r hr I hI hrI h3).hom ≫
    polynomialOppositeInitialInclusion W s b3 b4 b6 r

instance polynomialOppositeNodeChart_isOpenImmersion :
    IsOpenImmersion (polynomialOppositeNodeChart W s b3 b4 b6 r hr I hI hrI h3) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The opposite chart is the reflection followed by the constructed full evaluation. -/
theorem polynomialOppositeNodeChart_eq_spec :
    polynomialOppositeNodeChart W s b3 b4 b6 r hr I hI hrI h3 =
      Spec.map (CommRingCat.ofHom
        ((polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3).comp
          ((initialReflection W s b3 b4 b6).restrictScalars R).toAlgHom).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact polynomialOppositeNodeEquiv_base W s b3 b4 b6 r hr I hI hrI h3 z

/-- The opposite full chart retains the original coefficient morphism. -/
@[reassoc] theorem polynomialOppositeNodeChart_structure :
    polynomialOppositeNodeChart W s b3 b4 b6 r hr I hI hrI h3 ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)) =
        Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
  rw [polynomialOppositeNodeChart_eq_spec, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact ((polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3).comp
    ((initialReflection W s b3 b4 b6).restrictScalars R).toAlgHom).commutes z

/-- The first node chart has exactly the original first denominator open as image. -/
theorem polynomialNodeChart_range :
    Set.range (polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3) =
      (PrimeSpectrum.basicOpen
        (polynomialSmallFactor W s b3 b4 b6 r + algebraMap R A W.a₁) : Set (PrimeSpectrum A)) := by
  change Set.range (polynomialInitialOpenInclusion W s b3 b4 b6 r ∘
    (polynomialNodeIso W s b3 b4 b6 r hr I hI hrI h3).hom) = _
  exact ((polynomialNodeIso W s b3 b4 b6 r hr I hI hrI h3).hom.homeomorph.surjective.range_comp
    _).trans (PrimeSpectrum.localization_away_comap_range _ _)

/-- The opposite chart has exactly the reflected denominator open as image. -/
theorem polynomialOppositeNodeChart_range :
    Set.range (polynomialOppositeNodeChart W s b3 b4 b6 r hr I hI hrI h3) =
      (PrimeSpectrum.basicOpen (polynomialOppositeDenominator W s b3 b4 b6 r) :
        Set (PrimeSpectrum A)) := by
  change Set.range (polynomialOppositeInitialInclusion W s b3 b4 b6 r ∘
    (polynomialOppositeNodeIso W s b3 b4 b6 r hr I hI hrI h3).hom) = _
  have h := (polynomialOppositeNodeIso W s b3 b4 b6 r hr I hI hrI h3).hom.homeomorph.surjective
  exact (h.range_comp _).trans (PrimeSpectrum.localization_away_comap_range _ _)

/-- Both constructed full node charts cover every point of the original initial scheme. -/
theorem polynomialNodeCharts_cover (ha : IsUnit W.a₁) (p : Spec (.of A)) :
    p ∈ Set.range (polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3) ∨
      p ∈ Set.range (polynomialOppositeNodeChart W s b3 b4 b6 r hr I hI hrI h3) := by
  rw [polynomialNodeChart_range, polynomialOppositeNodeChart_range]
  exact polynomialNodeDenominators_cover W s b3 b4 b6 r I hI ha hrI h3 p

end FLT.Mazur.WeierstrassModificationX
