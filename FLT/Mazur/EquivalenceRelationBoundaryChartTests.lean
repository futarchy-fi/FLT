/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryOpenCoefficients

/-!
# Exact boundary chart tests over arbitrary schemes

A chart-valued point whose endpoint factors through the original boundary
factors through the entire chart boundary. Boundary coefficient identities
therefore hold on every such test, including nonreduced schemes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source boundary
variable {D A B T : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  {I : Type} [Fintype I] (o : I) (i : B ⟶ A)
  (U : (source p q I o).Opens) (E : B.Opens)
local notation "j" => inclusion (p := p) (q := q) I o i
local notation "b" => endpoint (p := p) (q := q) I o i
variable (u : T ⟶ U.toScheme) (w : T ⟶ E.toScheme)
  (hw : u ≫ U.ι ≫ first p q I o = w ≫ E.ι ≫ i)
/-- The original test square gives a map to the exact boundary pullback. -/
def boundaryTestLift : T ⟶ boundary (p := p) (q := q) I o i := by
  unfold boundary
  exact pullback.lift (u ≫ U.ι) (w ≫ E.ι)
    ((Category.assoc _ _ _).trans (hw.trans (Category.assoc _ _ _).symm))

/-- The typed boundary lift retains the ambient frame. -/
@[reassoc] theorem boundaryTestLift_ambient :
    boundaryTestLift o i U E u w hw ≫ j = u ≫ U.ι := by
  unfold boundaryTestLift inclusion boundary
  exact pullback.lift_fst (f := first p q I o) (g := i) (u ≫ U.ι) (w ≫ E.ι)
    ((Category.assoc _ _ _).trans (hw.trans (Category.assoc _ _ _).symm))

/-- The typed boundary lift retains the original closed endpoint. -/
@[reassoc] theorem boundaryTestLift_endpoint :
    boundaryTestLift o i U E u w hw ≫ b = w ≫ E.ι := by
  unfold boundaryTestLift endpoint boundary
  exact pullback.lift_snd (f := first p q I o) (g := i) (u ≫ U.ι) (w ≫ E.ι)
    ((Category.assoc _ _ _).trans (hw.trans (Category.assoc _ _ _).symm))

attribute [local irreducible] boundaryTestLift
local notation "l" => boundaryTestLift o i U E u w hw

/-- The exact pullback lift lands in the whole boundary of the chosen source chart. -/
theorem boundaryLift_range : Set.range l ⊆ Set.range ((j) ⁻¹ᵁ U).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  change (j) (l x) ∈ U
  have h := congrArg (fun g ↦ g x) (boundaryTestLift_ambient o i U E u w hw)
  exact h.symm ▸ (u x).property

/-- Actual factorization through the exact closed chart boundary. -/
def boundaryChartLift : T ⟶ ((j) ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift _ l (boundaryLift_range o i U E u w hw)

/-- The factorization retains the original boundary morphism. -/
@[reassoc] theorem boundaryChartLift_inclusion :
    boundaryChartLift o i U E u w hw ≫ ((j) ⁻¹ᵁ U).ι = l :=
  IsOpenImmersion.lift_fac _ l (boundaryLift_range o i U E u w hw)

/-- The ambient chart-valued test is unchanged. -/
@[reassoc] theorem boundaryChartLift_ambient :
    boundaryChartLift o i U E u w hw ≫ ((j) ∣_ U) = u := by
  apply (cancel_mono U.ι).mp
  simp only [Category.assoc, morphismRestrict_ι, boundaryChartLift_inclusion_assoc,
    boundaryTestLift_ambient]

/-- The original open boundary endpoint is unchanged. -/
@[reassoc] theorem boundaryChartLift_endpoint
    (hUE : (j) ⁻¹ᵁ U ≤ (b) ⁻¹ᵁ E) :
    boundaryChartLift o i U E u w hw ≫ (b).resLE E _ hUE = w := by
  apply (cancel_mono E.ι).mp
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, boundaryChartLift_inclusion_assoc,
    boundaryTestLift_endpoint]

include hw in
/-- Exact chart-boundary agreement holds on every scheme test over the original boundary. -/
theorem boundary_coefficient_test (hUE : (j) ⁻¹ᵁ U ≤ (b) ⁻¹ᵁ E)
    (s : Γ(U.toScheme, ⊤)) (t : Γ(E.toScheme, ⊤))
    (h : ((j) ∣_ U).appTop s = ((b).resLE E _ hUE).appTop t) :
    u.appTop s = w.appTop t := by
  have he := congrArg (fun z ↦ (boundaryChartLift o i U E u w hw).appTop z) h
  simpa only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
    boundaryChartLift_ambient, boundaryChartLift_endpoint] using he

end FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
