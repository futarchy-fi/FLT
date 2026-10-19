/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationDoubleVanishingOpen
public import FLT.Mazur.EquivalenceRelationCompleteScalarFiber

/-!+# Full original equations on arbitrary complete-supported tests

Only the first endpoint's support must be complete. The test scheme can have
arbitrary nilpotents, and the second endpoint is unrestricted in the original
chart. Factorization through an ambient zero-germ open gives exact equations.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ U = U)
local notation "k" => U.ι ≫ first p q I o
local notation "F" => SchemeRelationRestriction.fst p q k
local notation "H" => SchemeRelationRestriction.snd p q k
local notation "Rel" => SchemeRelationRestriction.doubleDomain p q k
local notation "ρ" => restrictedAction (action e I o) U hU

/-- Complete support suffices for exact equations on a full, possibly nonreduced, test. -/
theorem completeSupportedTest_equalizes [IsLocallyNoetherian A]
    {T : Scheme} (g : T ⟶ Rel)
    (hg : Set.range (g ≫ F ≫ U.ι) ⊆ completePointLocus (p := p) (q := q) I o)
    (t : invariantCoordinates ρ) :
    (g ≫ F).appTop t.val = (g ≫ H).appTop t.val := by
  let V := completeDoubleRelationVanishingOpen e I o U hU
  have hr : Set.range g ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact completeDoubleRelationVanishingOpen_contains e I o U hU
      (hg ⟨x, rfl⟩)
  let l := IsOpenImmersion.lift V.ι g hr
  have hl : l ≫ V.ι = g := IsOpenImmersion.lift_fac V.ι g hr
  have he := congrArg (fun a ↦ l.appTop a)
    (completeDoubleRelationVanishingOpen_equalizes e I o U hU t)
  change (l ≫ V.ι ≫ F).appTop t.val = (l ≫ V.ι ≫ H).appTop t.val at he
  simpa only [← Category.assoc, hl] using he

/-- The full quotient support controls exact equations without choosing source characters. -/
theorem completeOrbitSupportedTest_equalizes [IsLocallyNoetherian A] [IsAffine U.toScheme]
    {T : Scheme} (g : T ⟶ Rel)
    (hg : Set.range (g ≫ F ≫ quotientMap ρ) ⊆
      (completeAffineOrbitImage e I o U hU : Set (quotient ρ)))
    (t : invariantCoordinates ρ) :
    (g ≫ F).appTop t.val = (g ≫ H).appTop t.val := by
  apply completeSupportedTest_equalizes e I o U hU g _ t
  rintro _ ⟨x, rfl⟩
  have hx := hg ⟨x, rfl⟩
  change (g ≫ F) x ∈ quotientMap ρ ⁻¹'
    (completeAffineOrbitImage e I o U hU : Set (quotient ρ)) at hx
  rw [completeAffineOrbitImage_preimage] at hx
  exact hx

end FLT.Mazur.EquivalenceRelationNormalizedFrames
