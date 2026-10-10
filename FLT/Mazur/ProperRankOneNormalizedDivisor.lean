/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankOneDirectImageSection
public import FLT.Mazur.RelativeRankOneDivisorUniqueness
public import FLT.Mazur.ProperFamilySplitDirectImageSections

/-!
# The canonical full divisor of a rank-one direct image

Inverse biduality of the actual direct image constructs a relative section
on every test scheme. Its full zero ideal is the unique relative Cartier
divisor in the original Abel fiber; existence is constructed, not assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve LineSectionBaseChange
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
variable {P X T S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] [GeometricallyIntegral f] (h : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))
  (hN : LocallyFreeRankOne ((pushforward q).obj ((pullback p).obj L)))

/-- The intrinsic normalized relative section on the actual original test family. -/
@[irreducible] def rankOneFamilySection :
    RelativeSection q ((pullback p).obj L) (hL.pullback p) :=
  (rankOneSplitSection q ((pullback p).obj L) hN).toFamilyRelative h L hL hV

/-- The actual full Cartier divisor obtained from the normalized original section. -/
@[irreducible] def rankOneFamilyDivisor :
    RelativeFiber q ((pullback p).obj L) (hL.pullback p) :=
  relativeSectionToFiber q ((pullback p).obj L) (hL.pullback p)
    (rankOneFamilySection h L hL hV hN)

/-- The constructed divisor is the full zero ideal of the normalized original section. -/
lemma rankOneFamilyDivisor_ideal :
    (rankOneFamilyDivisor h L hL hV hN).val.val.val =
      lineSectionZeroIdeal (twist_rankOne q ((pullback p).obj L) (hL.pullback p)
        (rankOneFamilySection h L hL hV hN).val.baseLine)
        (rankOneFamilySection h L hL hV hN).val.section_ := by
  unfold rankOneFamilyDivisor
  rfl

/-- Every independently supplied divisor equals the constructed full normalized divisor. -/
theorem rankOneFamilyDivisor_unique
    (D : RelativeFiber q ((pullback p).obj L) (hL.pullback p)) :
    D = rankOneFamilyDivisor h L hL hV hN := by
  let _ : Surjective q := MorphismProperty.of_isPullback h inferInstance
  let _ := rankOne_relativeFiber_subsingleton q ((pullback p).obj L) (hL.pullback p) hN
  exact Subsingleton.elim _ _

/-- The relative Abel fiber is inhabited and unique on each unrestricted rank-one test. -/
@[instance_reducible] def rankOneFamilyFiberUnique :
    Unique (RelativeFiber q ((pullback p).obj L) (hL.pullback p)) where
  default := rankOneFamilyDivisor h L hL hV hN
  uniq := rankOneFamilyDivisor_unique h L hL hV hN

end FLT.Mazur.CartierAbel
