/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.FramedQuotientIdeal
public import FLT.Deformations.DeSmitLenstra.ProfiniteUniversalLift

/-!
# A specified local quotient of the actual universal framed deformation

The parameter ring and representation are the constructed profinite universal
objects. The residual row proves properness; maps from the quotient classify
continuous framed lifts with the specified local quotient coordinate.
-/

@[expose] public noncomputable section
open CategoryTheory IsLocalRing
namespace Deformation
open ProartinianCat
universe u
variable (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  (n : Type) [Fintype n] [DecidableEq n] [Finite (ResidueField O)]
  (ρ₀ : G →ₜ* GL n (residueField (𝓞 := O)))
  {H : Type u} [Group H] (ι : H →* G) (χ : H →* Oˣ) (q : n)

/-- The actual universal representation restricted to the specified local group. -/
def universalLocalQuotientIdeal : Ideal (profiniteFramedLimitObject O G n ρ₀) :=
  framedQuotientIdeal (profiniteFramedLimitObject O G n ρ₀)
    ((profiniteUniversalLift O G n ρ₀).comp ι) χ q

omit [TotallyDisconnectedSpace G] in
/-- The local equations define a closed ideal of the actual universal ring. -/
theorem universalLocalQuotientIdeal_closed :
    IsClosed (universalLocalQuotientIdeal O G n ρ₀ ι χ q :
      Set (profiniteFramedLimitObject O G n ρ₀)) :=
  framedQuotientIdeal_closed _ _ _ _

variable (hrow : ∀ g j, ρ₀ (ι g) q j =
  if j = q then algebraMap O (residueField (𝓞 := O)) (χ g : O) else 0)

include hrow
omit [TotallyDisconnectedSpace G] in
/-- The given residual quotient supplies a solution, so the universal ideal is proper. -/
theorem universalLocalQuotientIdeal_ne_top :
    universalLocalQuotientIdeal O G n ρ₀ ι χ q ≠ ⊤ := by
  apply framedQuotientIdeal_ne_top _ _ _ _
    (toResidueField (profiniteFramedLimitObject O G n ρ₀))
  intro g j
  have h := congrArg (fun r : G →* GL n (residueField (𝓞 := O)) ↦ r (ι g) q j)
    (profiniteUniversalContinuousLift_isFramedLift O G n ρ₀)
  exact h.trans (hrow g j)

/-- The local closed quotient, constructed without a nonzero-lift hypothesis. -/
def universalLocalQuotientObject : ProartinianCat O :=
  closedIdealQuotient (profiniteFramedLimitObject O G n ρ₀)
    (universalLocalQuotientIdeal O G n ρ₀ ι χ q)
    (universalLocalQuotientIdeal_closed O G n ρ₀ ι χ q)
    (universalLocalQuotientIdeal_ne_top O G n ρ₀ ι χ q hrow)

/-- Maps from the quotient are exactly continuous framed lifts with the local row condition. -/
def universalLocalQuotientEquiv (A : ProartinianCat O) :
    (universalLocalQuotientObject O G n ρ₀ ι χ q hrow ⟶ A) ≃
      {τ : ContinuousFramedLifts O G n ρ₀ A // ∀ g j,
        τ.val (ι g) q j = if j = q then algebraMap O A (χ g : O) else 0} :=
  (framedQuotientFactorEquiv (profiniteFramedLimitObject O G n ρ₀)
    ((profiniteUniversalLift O G n ρ₀).comp ι) χ q
    (universalLocalQuotientIdeal_ne_top O G n ρ₀ ι χ q hrow) A).trans
      ((profiniteFramedLimitHomEquiv O G n ρ₀ A).subtypeEquiv
        (p := fun f ↦ ∀ g j, f.hom (profiniteUniversalLift O G n ρ₀ (ι g) q j) =
          if j = q then algebraMap O A (χ g : O) else 0)
        (q := fun τ ↦ ∀ g j, τ.val (ι g) q j =
          if j = q then algebraMap O A (χ g : O) else 0) fun _ ↦ Iff.rfl)

end Deformation
