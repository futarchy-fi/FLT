/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicUnmarkedSheaf
public import FLT.Mazur.CyclicCharacteristicQuotientUnmarkedDescent

/-!
# Scheme-valued invariants of the actual fppf quotient

An invariant pair of actual chart morphisms gives a unique morphism from
the constructed sheaf to the sheaf represented by its target scheme.
The same datum factors through the existing finite quotient with exactly
its residual full unmarked invariance condition. This is a universal
property for maps into schemes, not a scheme representation assertion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {Y : Scheme}
  (v : ∀ b, normalizedLocus n b ⟶ Y)

/-- Evaluate actual chart morphisms on a normalized parameter of either characteristic. -/
def schemeParameterMap : normalizedParameterPresheaf n ⟶ uliftYoneda.{1}.obj Y where
  app _ := ↾(fun q ↦ ULift.up (q.2.down ≫ v q.1))
  naturality _ _ _ := by
    ext q
    exact congrArg ULift.up (Category.assoc _ _ _)

/-- Natural invariance here is precisely the original full geometric comparison predicate. -/
theorem schemeParameterMap_invariant_iff :
    ParameterInvariant n (schemeParameterMap n v) ↔ UnmarkedInvariant n v := by
  constructor
  · intro h T b c q r hqr
    exact congrArg ULift.down (h T ⟨b, ULift.up q⟩ ⟨c, ULift.up r⟩ hqr)
  · intro h T q r hqr
    exact congrArg ULift.up (h T q.1 r.1 q.2.down r.2.down hqr)

variable (hv : UnmarkedInvariant n v)

/-- A proved scheme-valued invariant descends to the actual sheaf quotient. -/
def unmarkedSchemeDesc :
    unmarkedParameterSheaf n ⟶ Scheme.fppfTopology.uliftYoneda.{1}.obj Y :=
  unmarkedSheafDesc n (schemeParameterMap n v)
    ((schemeParameterMap_invariant_iff n v).mpr hv)

/-- Descent gives the prescribed morphism on every original parameter. -/
theorem unmarkedSchemeDesc_evaluation {T : Scheme} (b : Bool)
    (q : T ⟶ normalizedLocus n b) :
    (unmarkedSchemeDesc n v hv).hom.app (Opposite.op T)
      ((unmarkedParameterSheafMap n).app (Opposite.op T) ⟨b, ULift.up q⟩) =
        ULift.up (q ≫ v b) :=
  congrArg (fun a ↦ a.app (Opposite.op T) ⟨b, ULift.up q⟩)
    (unmarkedParameterSheafMap_desc n (F := Scheme.fppfTopology.uliftYoneda.{1}.obj Y)
      (schemeParameterMap n v)
      ((schemeParameterMap_invariant_iff n v).mpr hv))

include hv in
/-- Every scheme-valued unmarked invariant extends uniquely to the actual fppf quotient. -/
theorem unmarkedScheme_desc_existsUnique :
    ∃! d : unmarkedParameterSheaf n ⟶ Scheme.fppfTopology.uliftYoneda.{1}.obj Y,
      unmarkedParameterSheafMap n ≫ d.hom = schemeParameterMap n v :=
  unmarkedSheaf_desc_existsUnique n (F := Scheme.fppfTopology.uliftYoneda.{1}.obj Y)
    (schemeParameterMap n v)
    ((schemeParameterMap_invariant_iff n v).mpr hv)

/-- A sheaf factorization forces genuine full unmarked invariance of the chart morphisms. -/
theorem unmarkedInvariant_of_sheaf_factor
    (d : unmarkedParameterSheaf n ⟶ Scheme.fppfTopology.uliftYoneda.{1}.obj Y)
    (hd : unmarkedParameterSheafMap n ≫ d.hom = schemeParameterMap n v) :
    UnmarkedInvariant n v := by
  apply (schemeParameterMap_invariant_iff n v).mp
  intro T q r hqr
  have he : (unmarkedParameterSheafMap n).app (Opposite.op T) q =
      (unmarkedParameterSheafMap n).app (Opposite.op T) r :=
    congrArg ((unmarkedClassToSheaf n).app (Opposite.op T)) (Quotient.sound hqr)
  rw [← hd]
  exact congrArg (d.hom.app (Opposite.op T)) he

/-- Sheaf extension is equivalent to finite-quotient descent with its full residual condition. -/
theorem unmarkedSheaf_factor_iff_quotient_desc :
    (∃! d : unmarkedParameterSheaf n ⟶ Scheme.fppfTopology.uliftYoneda.{1}.obj Y,
      unmarkedParameterSheafMap n ≫ d.hom = schemeParameterMap n v) ↔
    ∃! k : normalizedDisjointQuotient n ⟶ Y,
      (∀ b, quotientUnmarkedPullback n k b = v b) ∧ QuotientUnmarkedInvariant n k := by
  rw [← unmarkedInvariant_iff_quotient_desc]
  constructor
  · rintro ⟨d, hd, _⟩
    exact unmarkedInvariant_of_sheaf_factor n v d hd
  · exact unmarkedScheme_desc_existsUnique n v

end FLT.Mazur.CyclicCharacteristicAtlas
