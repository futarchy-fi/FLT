/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothTranslationOriginalInvariantDescent
public import FLT.Mazur.VariableHilbertInvariantOpenDescent
public import FLT.Mazur.SmoothTranslationInvariantOpenDomains

/-!
# Original and full-chart invariant sheaf sections agree

Over every open contained in the smooth translation neighborhood, both actual
invariant sheaves have canonically isomorphic section rings. The comparison
passes through the identical common-source domain and the two proved smooth
covers. This does not assert scheme effectivity of either quotient.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.SchemeEffectiveEpiSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {Y A : Scheme.{u}} (p q : A ⟶ Y)

/-- Transport invariant functions across an equality of their actual source opens. -/
def relationOpenFunctionsCongr {U W : Y.Opens} (h : U = W)
    (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U) (hW : p ⁻¹ᵁ W = q ⁻¹ᵁ W) :
    relationOpenFunctions p q U hU ≃+* relationOpenFunctions p q W hW := by
  subst W
  exact RingEquiv.refl _

/-- Domain transport uses precisely the original structure-sheaf equality map. -/
theorem relationOpenFunctionsCongr_val {U W : Y.Opens} (h : U = W)
    (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U) (hW : p ⁻¹ᵁ W = q ⁻¹ᵁ W)
    (s : relationOpenFunctions p q U hU) :
    (relationOpenFunctionsCongr p q h hU hW s).val =
      Y.presheaf.map (eqToHom (congrArg op h)) s.val := by
  subst W
  simp only [eqToHom_refl, Y.presheaf.map_id]
  rfl

end FLT.Mazur.SchemeEffectiveEpiSections
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Smooth V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  (O : TopologicalSpace.Opens (Orbit (smoothHilbertEquivalenceRelation f hL)))
  (hO : O ≤ smoothTranslationOrbitOpen f hL d V c)

/-- Original invariant sheaf sections map to common-source invariant functions. -/
def smoothTranslationOriginalSectionEquiv :
    (invariantSheaf (smoothHilbertEquivalenceRelation f hL)).obj.obj (op O) ≃+*
      relationOpenFunctions (baseOpenRestrictedFst f hL d V c).left
        (baseOpenRestrictedSnd f hL d V c).left
        ((variableSourceParameter f hL d V c).left ⁻¹ᵁ
          smoothTranslationParameterOpen f hL d V c O)
        (variableCommonSourceOpen_invariant f hL d V c _
          (smoothTranslationParameterOpen_invariant f hL d V c O)) :=
  (invariantSectionRingEquiv (smoothHilbertEquivalenceRelation f hL) O).trans
    ((smoothTranslationOriginalInvariantRingEquiv f hL d V c _
      (pullOpen_preimage_eq (smoothHilbertEquivalenceRelation f hL) O)
      (smoothTranslationPullOpen_le f hL d V c O hO)).trans
        (relationOpenFunctionsCongr _ _ (smoothTranslationCommonOpen_eq f hL d V c O)
          (originalCommonSourceOpen_invariant f hL d V c _
            (pullOpen_preimage_eq (smoothHilbertEquivalenceRelation f hL) O))
          (variableCommonSourceOpen_invariant f hL d V c _
            (smoothTranslationParameterOpen_invariant f hL d V c O))))

/-- The actual full-chart invariant sheaf has the same common-source section ring. -/
def smoothTranslationChartSectionEquiv :
    (invariantSheaf (variableChartEquivalenceRelation f hL d V c)).obj.obj
        (op (smoothTranslationFullChartOrbitOpen f hL d V c O)) ≃+*
      relationOpenFunctions (baseOpenRestrictedFst f hL d V c).left
        (baseOpenRestrictedSnd f hL d V c).left
        ((variableSourceParameter f hL d V c).left ⁻¹ᵁ
          smoothTranslationParameterOpen f hL d V c O)
        (variableCommonSourceOpen_invariant f hL d V c _
          (smoothTranslationParameterOpen_invariant f hL d V c O)) :=
  (invariantSectionRingEquivOn (variableChartEquivalenceRelation f hL d V c)
    (smoothTranslationFullChartOrbitOpen f hL d V c O) _
    (smoothTranslationFullChartOrbitOpen_pull f hL d V c O)
    (smoothTranslationParameterOpen_invariant f hL d V c O)).trans
      (variableChartOpenInvariantRingEquiv f hL d V c _
        (smoothTranslationParameterOpen_invariant f hL d V c O))

/-- Both actual invariant sheaves have the same sections on every neighborhood subopen. -/
def smoothTranslationInvariantSectionRingEquiv :
    (invariantSheaf (smoothHilbertEquivalenceRelation f hL)).obj.obj (op O) ≃+*
      (invariantSheaf (variableChartEquivalenceRelation f hL d V c)).obj.obj
        (op (smoothTranslationFullChartOrbitOpen f hL d V c O)) :=
  (smoothTranslationOriginalSectionEquiv f hL d V c O hO).trans
    (smoothTranslationChartSectionEquiv f hL d V c O).symm

/-- The invariant-sheaf comparison preserves the actual common-source invariant function. -/
theorem smoothTranslationInvariantSectionRingEquiv_common
    (s : (invariantSheaf (smoothHilbertEquivalenceRelation f hL)).obj.obj (op O)) :
    smoothTranslationChartSectionEquiv f hL d V c O
        (smoothTranslationInvariantSectionRingEquiv f hL d V c O hO s) =
      smoothTranslationOriginalSectionEquiv f hL d V c O hO s :=
  (smoothTranslationChartSectionEquiv f hL d V c O).apply_symm_apply _

/-- The original-side equivalence retains actual source pullback and domain transport. -/
theorem smoothTranslationOriginalSectionEquiv_val
    (s : (invariantSheaf (smoothHilbertEquivalenceRelation f hL)).obj.obj (op O)) :
    (smoothTranslationOriginalSectionEquiv f hL d V c O hO s).val =
      (variableSourceIntersection f hL d V c).left.presheaf.map
        (eqToHom (congrArg op (smoothTranslationCommonOpen_eq f hL d V c O)))
        ((variableSourceInclusion f hL d V c).left.app
          (pullOpen (smoothHilbertEquivalenceRelation f hL) O).val
          ((invariantInclusion (smoothHilbertEquivalenceRelation f hL)).hom.app (op O) s)) := by
  dsimp only [smoothTranslationOriginalSectionEquiv, RingEquiv.trans_apply]
  rw [relationOpenFunctionsCongr_val]
  exact congrArg _ (smoothTranslationOriginalInvariantRingEquiv_val f hL d V c _
    (pullOpen_preimage_eq (smoothHilbertEquivalenceRelation f hL) O)
    (smoothTranslationPullOpen_le f hL d V c O hO)
    (invariantSectionRingEquiv (smoothHilbertEquivalenceRelation f hL) O s))

/-- The chart-side equivalence retains actual parameter pullback and domain transport. -/
theorem smoothTranslationChartSectionEquiv_val
    (s : (invariantSheaf (variableChartEquivalenceRelation f hL d V c)).obj.obj
      (op (smoothTranslationFullChartOrbitOpen f hL d V c O))) :
    (smoothTranslationChartSectionEquiv f hL d V c O s).val =
      (variableSourceParameter f hL d V c).left.app
        (smoothTranslationParameterOpen f hL d V c O)
        ((variableHilbertTest f d V).left.presheaf.map
          (eqToHom (congrArg op (smoothTranslationFullChartOrbitOpen_pull f hL d V c O)))
          ((invariantInclusion (variableChartEquivalenceRelation f hL d V c)).hom.app
            (op (smoothTranslationFullChartOrbitOpen f hL d V c O)) s)) := by
  dsimp only [smoothTranslationChartSectionEquiv, RingEquiv.trans_apply]
  exact (variableChartOpenInvariantRingEquiv_val f hL d V c _
    (smoothTranslationParameterOpen_invariant f hL d V c O) _).trans
      (congrArg _ (invariantSectionRingEquivOn_val
        (variableChartEquivalenceRelation f hL d V c)
        (smoothTranslationFullChartOrbitOpen f hL d V c O) _
        (smoothTranslationFullChartOrbitOpen_pull f hL d V c O)
        (smoothTranslationParameterOpen_invariant f hL d V c O) s))

end FLT.Mazur.HilbertChart
