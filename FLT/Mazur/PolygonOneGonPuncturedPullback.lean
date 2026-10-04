/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePullbackIntersection
public import FLT.Mazur.PolygonNodeRingComparison
public import FLT.Mazur.PolygonOneGonTorusIntersection

/-!
# The actual refined one-gon overlap ring

Pull back the chosen B denominator through the punctured normalization and
paste with the genuine torus gluing square. The resulting ring is localized
at the original denominator evaluated in K[t,1/(t(t-1))].
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonNodeAffineCharts
open PolygonPinching PolygonNodePresentation OneGonTransition
open PrincipalAffineRefinement LocalizationJointRestriction
variable (K : Type u) [Field K] (hn : 0 < 1)
  {C : Over (Spec (.of K))} (p : components K 1 ⟶ C) (q : nodes K 1 ⟶ C)
  (h : IsPushout (toComponents K 1 hn) (toNodes K 1) p q)
  (a : Fin 1 → Kˣ) (x : Spec (.of K))

/-- The precise punctured normalization localization is the actual torus pullback. -/
lemma one_punctured_isPullback (i : Fin 1) :
    let s := oneDenominator K hn p q h a x
    IsPullback (Spec.map (CommRingCat.ofHom (restriction bPunctureMap s)))
      (inclusion (bPunctureMap s) ≫ toTorus K)
      (oneDenominatorChart K hn p q h a x)
      (torusToComponent K ≫ componentι K 1 i ≫ p).left := by
  dsimp only
  exact (PrincipalLocalizationPullback.isPullback bPunctureMap _).flip.paste_vert
    (one_torus_isPullback K hn p q h i)

/-- Regular functions on the actual node/torus intersection have the punctured B_f ring. -/
def oneIntersectionSectionsIso (i : Fin 1) :
    let := torus_isOpenImmersion K 1 hn p q h i
    let s := oneDenominator K hn p q h a x
    Γ(C.left, (oneDenominatorChart K hn p q h a x ''ᵁ ⊤) ⊓
      ((torusToComponent K ≫ componentι K 1 i ≫ p).left ''ᵁ ⊤)) ≅
      CommRingCat.of (Localization.Away (bPunctureMap s)) := by
  let := torus_isOpenImmersion K 1 hn p q h i
  exact AffinePullbackIntersection.sectionsIso _ _ _ _
    (one_punctured_isPullback K hn p q h a x i)

/-- The second ring map is the localization of the actual Möbius transition. -/
lemma one_punctured_spec_isPullback (i : Fin 1) :
    let s := oneDenominator K hn p q h a x
    IsPullback (Spec.map (CommRingCat.ofHom (restriction bPunctureMap s)))
      (Spec.map (CommRingCat.ofHom
        ((algebraMap (puncture K) (Localization.Away (bPunctureMap s))).comp (overlapMap K))))
      (oneDenominatorChart K hn p q h a x)
      (torusToComponent K ≫ componentι K 1 i ≫ p).left := by
  simpa only [inclusion, CommRingCat.ofHom_comp, Spec.map_comp, toTorus_eq_specMap] using
    one_punctured_isPullback K hn p q h a x i

end FLT.Mazur.PolygonNodeAffineCharts
