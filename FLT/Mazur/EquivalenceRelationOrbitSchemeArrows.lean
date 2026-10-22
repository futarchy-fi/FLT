/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationOriginalOrbitComparison
public import FLT.Mazur.SchemeScalarOrbitEndpoints

/-!
# Original relation arrows on the full normalized orbit spectrum

Glue the actual moving-endpoint arrows across the finite product spectrum.
This gives a scheme arrow with both original endpoints, valid on all
coefficient schemes rather than only on field-valued characters.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeScalarOrbitComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme]
local notation "ρ" => restrictedAction (action e I o) U hU
set_option quotPrecheck false
local notation "C" => Γ(U.toScheme, ⊤)

/-- The full product spectrum maps to the original relation by its actual action arrows. -/
def originalOrbitArrow : Spec (.of (Equiv.Perm I → C)) ⟶ D :=
  inv (sigmaSpec (fun _ : Equiv.Perm I ↦ C)) ≫
    Sigma.desc (fun g ↦ U.toScheme.isoSpec.inv ≫ U.ι ≫ actionArrow I o g⁻¹)

/-- On each component the glued arrow is the literal inverse permutation arrow. -/
@[reassoc] theorem orbitComponent_originalOrbitArrow (g : Equiv.Perm I) :
    orbitComponent (X := U.toScheme) g ≫ originalOrbitArrow I o U =
      U.toScheme.isoSpec.inv ≫ U.ι ≫ actionArrow I o g⁻¹ := by
  unfold orbitComponent originalOrbitArrow
  rw [← ι_sigmaSpec, Category.assoc, IsIso.hom_inv_id_assoc, Sigma.ι_comp_desc]

attribute [local irreducible] originalOrbitArrow orbitMap tensorFirst tensorSecond

variable {R : Type} [CommRing R]
  (s : R →+* invariantCoordinates (restrictedAction (action e I o) U hU))

/-- The first tensor endpoint agrees with the original relation's first endpoint. -/
@[reassoc] theorem originalOrbitArrow_first :
    originalOrbitArrow I o U ≫ p =
      orbitMap ρ s ≫ tensorFirst ρ s ≫ U.ι ≫ first p q I o := by
  apply orbitComponent_hom_ext
  intro g
  rw [orbitComponent_originalOrbitArrow_assoc,
    actionArrow_first, orbitComponent_first_assoc]

/-- The independent second tensor endpoint agrees with the original second endpoint. -/
@[reassoc] theorem originalOrbitArrow_second :
    originalOrbitArrow I o U ≫ q =
      orbitMap ρ s ≫ tensorSecond ρ s ≫ U.ι ≫ first p q I o := by
  apply orbitComponent_hom_ext
  intro g
  rw [orbitComponent_originalOrbitArrow_assoc,
    actionArrow_second e, orbitComponent_second_assoc, restrictedAction_hom_ι_assoc]

/-- Every orbit-spectrum test constructs an actual original arrow with both specified endpoints. -/
theorem orbit_test_original_arrow {T : Scheme.{0}}
    (t : T ⟶ tensorScheme ρ s)
    (w : T ⟶ Spec (.of (Equiv.Perm I → C))) (hw : w ≫ orbitMap ρ s = t) :
    ∃! d : T ⟶ D,
      d ≫ p = t ≫ tensorFirst ρ s ≫ U.ι ≫ first p q I o ∧
      d ≫ q = t ≫ tensorSecond ρ s ≫ U.ι ≫ first p q I o := by
  refine ⟨w ≫ originalOrbitArrow I o U, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, originalOrbitArrow_first e I o U hU s, ← Category.assoc w, hw]
  · rw [Category.assoc, originalOrbitArrow_second e I o U hU s, ← Category.assoc w, hw]
  · intro d hd
    apply e.right_cancellation
    · rw [hd.1, Category.assoc, originalOrbitArrow_first e I o U hU s,
        ← Category.assoc w, hw]
    · rw [hd.2, Category.assoc, originalOrbitArrow_second e I o U hU s,
        ← Category.assoc w, hw]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
