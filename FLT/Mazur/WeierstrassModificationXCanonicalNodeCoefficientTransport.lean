/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXCanonicalNodeCoefficientNaturality
public import FLT.Mazur.WeierstrassModificationXCoefficientTransport
public import FLT.Mazur.WeierstrassModificationXNodeOpenCoefficientTransport

/-!
# Canonical full initial node squares with explicitly identified target data

The lower curve and smoothing can be independently named. Both roots remain
independently constructed; only the original coefficient maps are transported.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (U : WeierstrassCurve S) (s' c3 c4 c6 : S)
  (hW : W.map f = U) (hs : f s = s') (hB3 : f b3 = c3)
  (hB4 : f b4 = c4) (hB6 : f b6 = c6)
  (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)
  (hI : IsNilpotent I) (hJ : IsNilpotent J) (ha : IsUnit W.a₁) (ha' : IsUnit U.a₁)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
  (h2' : U.a₂ ∈ J) (h3' : c3 ∈ J) (h4' : c4 ∈ J) (h6' : c6 ∈ J)
local notation "r₀" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hr₀" => polynomialSlopeRoot_equation W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hm₀" => polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "r₁" => polynomialSlopeRoot U c3 c4 c6 J hJ ha' h2' h3' h4' h6'
local notation "hr₁" => polynomialSlopeRoot_equation U c3 c4 c6 J hJ ha' h2' h3' h4' h6'
local notation "hm₁" => polynomialSlopeRoot_mem U c3 c4 c6 J hJ ha' h2' h3' h4' h6'
local notation "g" => Spec.map
  (CommRingCat.ofHom (nodeOpenCoefficientRingMapTo f W s U s' hW hs))
local notation "c" => Spec.map (CommRingCat.ofHom
  (coefficientRingMapTo f W s b3 b4 b6 U s' c3 c4 c6 hW hs hB3 hB4 hB6))
attribute [local irreducible] polynomialSlopeRoot polynomialNodeChart polynomialOppositeNodeChart
include hf

/-- The first full canonical node commutes with the explicitly identified coefficient target. -/
@[reassoc] theorem canonicalPolynomialNodeChart_coefficient_of_eq :
    g ≫ polynomialNodeChart W s b3 b4 b6 r₀ hr₀ I hI hm₀ h3 =
      polynomialNodeChart U s' c3 c4 c6 r₁ hr₁ J hJ hm₁ h3' ≫ c := by
  subst U s' c3 c4 c6
  exact canonicalPolynomialNodeChart_coefficient f W s b3 b4 b6 I J hf hI hJ ha h2 h3 h4 h6

/-- The opposite full canonical node commutes with the same explicit target. -/
@[reassoc] theorem canonicalPolynomialOppositeNodeChart_coefficient_of_eq :
    g ≫ polynomialOppositeNodeChart W s b3 b4 b6 r₀ hr₀ I hI hm₀ h3 =
      polynomialOppositeNodeChart U s' c3 c4 c6 r₁ hr₁ J hJ hm₁ h3' ≫ c := by
  subst U s' c3 c4 c6
  exact canonicalPolynomialOppositeNodeChart_coefficient
    f W s b3 b4 b6 I J hf hI hJ ha h2 h3 h4 h6

end FLT.Mazur.WeierstrassModificationX
