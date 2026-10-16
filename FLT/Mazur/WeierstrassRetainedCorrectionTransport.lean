/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedNodeFactorNaturality

/-!
# Full correction units with independently named coefficient targets

Every target coefficient is transported explicitly. This permits the actual
arithmetic quotient maps to act on independently constructed root units.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
universe u

/-- The complete correction follows a coefficient map with independently named target data. -/
theorem retainedFactorCorrectionUnit_map_of_eq
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    {W : WeierstrassCurve R} {W' : WeierstrassCurve S}
    {π s c3 c4 c6 : R} {π' s' c3' c4' c6' : S}
    {I : Ideal R} {J : Ideal S} {hI : IsNilpotent I} {hJ : IsNilpotent J}
    (hf : I ≤ J.comap f) {ha : IsUnit W.a₁} {ha' : IsUnit W'.a₁}
    {hs : s ∈ I} {h2 : W.a₂ ∈ I} {h3 : c3 ∈ I} {h4 : c4 ∈ I} {h6 : c6 ∈ I}
    {hs' : s' ∈ J} {h2' : W'.a₂ ∈ J} {h3' : c3' ∈ J} {h4' : c4' ∈ J}
    {h6' : c6' ∈ J}
    (hW : W.map f = W') (hπ : f π = π') (hS : f s = s')
    (h3c : f c3 = c3') (h4c : f c4 = c4') (h6c : f c6 = c6') :
    Units.map (ringMap f π π' hπ).toMonoidHom
        (retainedFactorCorrectionUnit W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6) =
      retainedFactorCorrectionUnit W' π' s' c3' c4' c6' J hJ ha' hs' h2' h3' h4' h6' := by
  subst W' π' s' c3' c4' c6'
  exact retainedFactorCorrectionUnit_map f W π s c3 c4 c6 I J hf
    hI hJ ha hs h2 h3 h4 h6

end FLT.Mazur.WeierstrassModificationX
