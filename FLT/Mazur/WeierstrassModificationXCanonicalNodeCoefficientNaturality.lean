/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXOppositeNodeCoefficientNaturality

/-!
# Both canonical full initial nodes commute with coefficient change

The target polynomial root is independently constructed in the target ideal.
Root uniqueness identifies it with the transported source root, so both full
initial node squares use the original canonical chart maps.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)
  (hI : IsNilpotent I) (hJ : IsNilpotent J) (ha : IsUnit W.a₁)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "U" => W.map f
local notation "r₀" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hr₀" => polynomialSlopeRoot_equation W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hm₀" => polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "r₁" => polynomialSlopeRoot U (f b3) (f b4) (f b6) J hJ
  (ha.map f) (hf h2) (hf h3) (hf h4) (hf h6)
local notation "hr₁" => polynomialSlopeRoot_equation U (f b3) (f b4) (f b6) J hJ
  (ha.map f) (hf h2) (hf h3) (hf h4) (hf h6)
local notation "hm₁" => polynomialSlopeRoot_mem U (f b3) (f b4) (f b6) J hJ
  (ha.map f) (hf h2) (hf h3) (hf h4) (hf h6)
local notation "g" => Spec.map (CommRingCat.ofHom (nodeOpenCoefficientRingMap f W s))
local notation "c" => Spec.map (CommRingCat.ofHom (coefficientRingMap f W s b3 b4 b6))
attribute [local irreducible] polynomialSlopeRoot polynomialNodeChart polynomialOppositeNodeChart

/-- The full small initial node square uses the independently constructed target root. -/
@[reassoc] theorem canonicalPolynomialNodeChart_coefficient :
    g ≫ polynomialNodeChart W s b3 b4 b6 r₀ hr₀ I hI hm₀ h3 =
      polynomialNodeChart U (f s) (f b3) (f b4) (f b6) r₁ hr₁ J hJ hm₁ (hf h3) ≫ c := by
  have he : Polynomial.map f r₀ = r₁ :=
    polynomialSlopeRoot_coefficient f W b3 b4 b6 I J hf hI hJ ha h2 h3 h4 h6
  simpa only [he] using
    polynomialNodeChart_coefficient f W s b3 b4 b6 r₀ hr₀ I J hf hI hJ hm₀ h3

/-- The full opposite initial node square uses that same independent target construction. -/
@[reassoc] theorem canonicalPolynomialOppositeNodeChart_coefficient :
    g ≫ polynomialOppositeNodeChart W s b3 b4 b6 r₀ hr₀ I hI hm₀ h3 =
      polynomialOppositeNodeChart U (f s) (f b3) (f b4) (f b6) r₁ hr₁ J hJ hm₁ (hf h3) ≫ c := by
  have he : Polynomial.map f r₀ = r₁ :=
    polynomialSlopeRoot_coefficient f W b3 b4 b6 I J hf hI hJ ha h2 h3 h4 h6
  simpa only [he] using
    polynomialOppositeNodeChart_coefficient f W s b3 b4 b6 r₀ hr₀ I J hf hI hJ hm₀ h3

end FLT.Mazur.WeierstrassModificationX
