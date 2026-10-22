/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationDoubleVanishingOpen
public import FLT.Mazur.EquivalenceRelationCompleteExactRank

/-!
# Full invariant equality on complete original-arrow tests

The uniform relation open pulls back to an entire test scheme when its first
frame is complete at every point. Equality of all invariant sections then
holds with nilpotents retained. An actual original arrow is indispensable.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A T : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [IsLocallyNoetherian A] (e : CategoryTheory.EquivalenceRelation p q)
  (I : Type) [Fintype I] (o : I) (U : (source p q I o).Opens)
  (hU : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ U = U)
attribute [local irreducible] source action SchemeRelationRestriction.doubleDomain
local notation "k" => U.ι ≫ first p q I o
local notation "F" => SchemeRelationRestriction.fst p q k
local notation "H" => SchemeRelationRestriction.snd p q k
local notation "ρ" => restrictedAction (action e I o) U hU

/-- Completeness makes every full invariant agree along the unchanged original arrow. -/
theorem invariant_eq_of_complete_original_arrow (u v : T ⟶ U.toScheme) (d : T ⟶ D)
    (hp : d ≫ p = u ≫ k) (hq : d ≫ q = v ≫ k)
    (hu : Set.range (u ≫ U.ι) ⊆ completePointLocus (p := p) (q := q) I o)
    (a : invariantCoordinates ρ) : u.appTop a.val = v.appTop a.val := by
  let l := SchemeRelationRestriction.lift p q k d u v hp hq
  let O := completeDoubleRelationVanishingOpen e I o U hU
  have hlF : l ≫ F = u := SchemeRelationRestriction.lift_fst p q k d u v hp hq
  have hlH : l ≫ H = v := SchemeRelationRestriction.lift_snd p q k d u v hp hq
  have hr : Set.range l ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    apply completeDoubleRelationVanishingOpen_contains e I o U hU
    change (l ≫ F ≫ U.ι) t ∈ completePointLocus (p := p) (q := q) I o
    rw [← Category.assoc, hlF]
    exact hu (Set.mem_range_self t)
  let w := IsOpenImmersion.lift O.ι l hr
  have hw : w ≫ O.ι = l := IsOpenImmersion.lift_fac O.ι l hr
  have ha := congrArg (fun b ↦ w.appTop b)
    (completeDoubleRelationVanishingOpen_equalizes e I o U hU a)
  change (w ≫ O.ι ≫ F).appTop a.val = (w ≫ O.ι ≫ H).appTop a.val at ha
  simpa only [← Category.assoc, hw, hlF, hlH] using ha

variable [QuasiCompact p]

local instance completeTestOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance completeTestOver_etale : Etale (Over.mk p).hom := ‹Etale p›

/-- The full exact-rank condition suffices, without any open-interior or reducedness input. -/
theorem invariant_eq_of_exactRank_original_arrow (n : ℕ) (o : Fin n)
    (U : (source p q (Fin n) o).Opens)
    (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
    (u v : T ⟶ U.toScheme) (d : T ⟶ D)
    (hp : d ≫ p = u ≫ U.ι ≫ first p q (Fin n) o)
    (hq : d ≫ q = v ≫ U.ι ≫ first p q (Fin n) o)
    (hu : Set.range (u ≫ U.ι ≫ first p q (Fin n) o) ⊆ exactRank (Over.mk p) n)
    (a : invariantCoordinates (restrictedAction (action e (Fin n) o) U hU)) :
    u.appTop a.val = v.appTop a.val := by
  apply invariant_eq_of_complete_original_arrow e (Fin n) o U hU u v d hp hq _ a
  rintro _ ⟨t, rfl⟩
  rw [completePointLocus_eq_rankAtMost_preimage]
  exact (hu (Set.mem_range_self t)).2

end FLT.Mazur.EquivalenceRelationNormalizedFrames
