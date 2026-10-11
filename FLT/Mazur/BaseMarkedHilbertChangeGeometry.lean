/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertChangePullback

/-!
# Local geometry of translation-base comparisons

The proved scheme pullback transports geometric properties of the actual base
map. These statements do not assume that any chosen translation bases cover
the original Picard quotient.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  {V W : Over (Spec (.of R))} (b : W ⟶ V)
  {ι : Type} (a : ι → BaseMarkedHilbertIndex f V)

/-- Every base-change-stable property of the base map holds for the glued comparison. -/
theorem baseMarkedGluedChange_property (P : MorphismProperty Scheme)
    [P.IsStableUnderBaseChange] (hb : P b.left) :
    P (baseMarkedGluedChange f hL b a).left :=
  MorphismProperty.of_isPullback (baseMarkedGluedChange_isPullback f hL b a).flip hb

instance baseMarkedGluedChange_isOpenImmersion [IsOpenImmersion b.left] :
    IsOpenImmersion (baseMarkedGluedChange f hL b a).left :=
  baseMarkedGluedChange_property f hL b a _ inferInstance

instance baseMarkedGluedChange_etale [Etale b.left] :
    Etale (baseMarkedGluedChange f hL b a).left :=
  baseMarkedGluedChange_property f hL b a _ inferInstance

instance baseMarkedGluedChange_smooth [Smooth b.left] :
    Smooth (baseMarkedGluedChange f hL b a).left :=
  baseMarkedGluedChange_property f hL b a _ inferInstance

instance baseMarkedGluedChange_flat [Flat b.left] :
    Flat (baseMarkedGluedChange f hL b a).left :=
  baseMarkedGluedChange_property f hL b a _ inferInstance

instance baseMarkedGluedChange_locallyOfFinitePresentation [LocallyOfFinitePresentation b.left] :
    LocallyOfFinitePresentation (baseMarkedGluedChange f hL b a).left :=
  baseMarkedGluedChange_property f hL b a _ inferInstance

/-- Surjectivity follows from the actual scheme pullback, without a pointwise product shortcut. -/
instance baseMarkedGluedChange_surjective [Surjective b.left] :
    Surjective (baseMarkedGluedChange f hL b a).left := by
  constructor
  intro x
  obtain ⟨y, hy⟩ := b.left.surjective ((baseMarkedGluedBase f hL V a).left x)
  obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
    (baseMarkedGluedChange_isPullback f hL b a) x y hy.symm
  exact ⟨z, hz⟩

/-- An actual fppf base morphism gives an actual fppf cover of the glued scheme. -/
theorem baseMarkedGluedChange_fppf [Flat b.left] [LocallyOfFinitePresentation b.left]
    [Surjective b.left] :
    Presieve.singleton (baseMarkedGluedChange f hL b a).left ∈
      Scheme.fppfPrecoverage (baseMarkedGluedTest f hL V a).left :=
  Scheme.Hom.singleton_mem_fppfPrecoverage _

end FLT.Mazur.HilbertChart
