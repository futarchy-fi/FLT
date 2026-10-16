/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedNodeFactorRatioNaturality

/-!
# Independently named targets in the full retained coefficient square

Transport identifies the original curve, every divided coefficient, and the
actual divisor. It does not identify two arbitrary choices of a divisor.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
universe u

/-- The full retained square accepts independent target data with a transported divisor. -/
@[reassoc] theorem retainedFactorRatioChart_coefficients_of_eq
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    {W : WeierstrassCurve R} {W' : WeierstrassCurve S}
    {π s c3 c4 c6 d : R} {π' s' c3' c4' c6' d' : S}
    {I : Ideal R} {J : Ideal S} {hI : IsNilpotent I} {hJ : IsNilpotent J}
    (hf : I ≤ J.comap f) {ha : IsUnit W.a₁} {ha' : IsUnit W'.a₁}
    {hs : s ∈ I} {h2 : W.a₂ ∈ I} {h3 : c3 ∈ I} {h4 : c4 ∈ I} {h6 : c6 ∈ I}
    {hs' : s' ∈ J} {h2' : W'.a₂ ∈ J} {h3' : c3' ∈ J} {h4' : c4' ∈ J}
    {h6' : c6' ∈ J} {hd : s = π * d} {hd' : s' = π' * d'}
    (hW : W.map f = W') (hπ : f π = π') (hS : f s = s')
    (h3c : f c3 = c3') (h4c : f c4 = c4') (h6c : f c6 = c6') (hD : f d = d')
    (hτ : f (initialTangentSmoothing W ha s) = initialTangentSmoothing W' ha' s') :
    Spec.map (CommRingCat.ofHom (ringMap f π π' hπ)) ≫
      retainedFactorRatioChart W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 d hd =
    retainedFactorRatioChart W' π' s' c3' c4' c6' J hJ ha' hs' h2' h3' h4' h6' d' hd' ≫
      Spec.map (CommRingCat.ofHom (ringMap f (initialTangentSmoothing W ha s)
        (initialTangentSmoothing W' ha' s') hτ)) := by
  subst W' π' s' c3' c4' c6' d'
  exact retainedFactorRatioChart_coefficients f W π s c3 c4 c6 I J hf
    hI hJ ha hs h2 h3 h4 h6 d hd

end FLT.Mazur.WeierstrassModificationX
