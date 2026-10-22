/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationOriginalChartScalars
public import FLT.Mazur.OriginalBoundaryComparisonClosedImage

/-!
# Normalized orbit tests factor the full original boundary comparison

The scalar map is the constructed pullback from the full original equalizer.
An orbit test with the two prescribed boundary endpoints constructs an arrow
in the entire original boundary relation. The result uses the actual boundary
ideal and arbitrary coefficient schemes, preserving nilpotents and both endpoints.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeScalarOrbitComparison
open EquivalenceRelationOrderedFrames RingPairInvariantFlatScalars
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction tensorFirst tensorSecond orbitMap
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme] (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
attribute [local instance] RingPairInvariantFlatScalars.sourceAlgebra
  targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "ρ" => restrictedAction (action e I o) U hU
local notation "s" => originalChartScalars e I o U hU
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
attribute [local irreducible] scalarMorphism

/-- An orbit factor constructs the unique lift through the full original boundary comparison. -/
theorem originalBoundary_of_orbit_test {T : Scheme.{0}}
    (z : T ⟶ pullback f f) (t : T ⟶ tensorScheme ρ s)
    (w : T ⟶ Spec (.of (Equiv.Perm I → Γ(U.toScheme, ⊤))))
    (hw : w ≫ orbitMap ρ s = t)
    (hx : t ≫ tensorFirst ρ s ≫ U.ι ≫ first p q I o =
      z ≫ pullback.fst f f ≫ J.subschemeι)
    (hy : t ≫ tensorSecond ρ s ≫ U.ι ≫ first p q I o =
      z ≫ pullback.snd f f ≫ J.subschemeι) :
    ∃! d : T ⟶ pullback p J.subschemeι, d ≫ c = z := by
  obtain ⟨a, ha, _⟩ := orbit_test_original_arrow e I o U hU s t w hw
  have hp : a ≫ p = (z ≫ pullback.fst f f) ≫ J.subschemeι := by
    simpa only [Category.assoc] using ha.1.trans hx
  have hq : a ≫ q = (z ≫ pullback.snd f f) ≫ J.subschemeι := by
    simpa only [Category.assoc] using ha.2.trans hy
  let d := pullback.lift a (z ≫ pullback.fst f f) hp
  have hd : d ≫ c = z := by
    apply pullback.hom_ext
    · simp only [d, originalBoundaryComparison, Category.assoc,
        pullback.lift_fst, pullback.lift_snd]
    · change d ≫ originalBoundaryComparison p q J hJ ≫ pullback.snd f f = _
      rw [originalBoundaryComparison, pullback.lift_snd]
      exact InvariantIdealRelation.lift_snd J p q hJ a _ _ hp hq
  let _ := originalBoundaryComparison_mono e J hJ
  exact ⟨d, hd, fun d' hd' ↦ (cancel_mono c).mp (hd'.trans hd.symm)⟩

include e in
omit [IsSeparated p] in
/-- Any independently constructed orbit lifts commute under exact coefficient-test transitions. -/
theorem originalBoundary_orbit_lifts_transition {T T' : Scheme.{0}}
    (z : T ⟶ pullback f f) (z' : T' ⟶ pullback f f)
    (v : T' ⟶ T) (hv : v ≫ z = z')
    (d : T ⟶ pullback p J.subschemeι) (d' : T' ⟶ pullback p J.subschemeι)
    (hd : d ≫ c = z) (hd' : d' ≫ c = z') : v ≫ d = d' := by
  let _ := originalBoundaryComparison_mono e J hJ
  apply (cancel_mono c).mp
  rw [Category.assoc, hd, hv, hd']

end FLT.Mazur.EquivalenceRelationNormalizedFrames
