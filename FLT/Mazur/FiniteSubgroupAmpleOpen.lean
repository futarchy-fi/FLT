/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperAmpleFiberOpen
public import FLT.Mazur.GeneralizedCurveAmpleBaseChange
public import FLT.Mazur.GeneralizedCurveCartierDescent

/-!
# The ample open of an actual Cartier subgroup

The open is cut out by ampleness of the original divisor line on residue fibers.
It represents exactly the base changes on which the original subgroup is ample.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ}
  (H : E.FiniteSubgroup n) (hI : EffectiveCartier H.ideal)

/-- Ampleness of the actual base-changed subgroup is ampleness of the pulled-back line. -/
theorem isAmple_baseChange_iff_line (g : T ⟶ S) :
    (H.baseChange g).IsAmple ↔ RelativeAmple (pullback.snd E.curve.hom g)
      ((Scheme.Modules.pullback (pullback.fst E.curve.hom g)).obj
        (divisorLineBundle H.ideal hI)) := by
  let _ := H.idealPullbackHom_isIso hI g
  constructor
  · rintro ⟨hJ, ha⟩
    exact ha.of_iso (divisorLinePullbackIsoOfEq (pullback.fst E.curve.hom g)
      hI hJ (H.baseChange_ideal g).symm)
  · intro ha
    let hJ := H.effectiveCartier_baseChange hI g
    exact ⟨hJ, ha.of_iso (divisorLinePullbackIsoOfEq (pullback.fst E.curve.hom g)
      hI hJ (H.baseChange_ideal g).symm).symm⟩

/-- The open of ample fibers of the original subgroup divisor. -/
def ampleOpen : S.Opens := by
  let _ := E.family.family.1
  exact properAmpleFiberOpen E.curve.hom (divisorLineBundle H.ideal hI)
    hI.divisorLineBundle_locallyFreeRankOne

/-- A base change is ample precisely when its entire image lies in the constructed open. -/
theorem isAmple_baseChange_iff_range (g : T ⟶ S) :
    (H.baseChange g).IsAmple ↔ Set.range g ⊆ H.ampleOpen hI := by
  let _ := E.family.family.1
  rw [H.isAmple_baseChange_iff_line hI g]
  exact relativeAmple_iff_range_ampleFiberOpen E.curve.hom _
    hI.divisorLineBundle_locallyFreeRankOne (IsPullback.of_hasPullback _ _)

/-- The original subgroup restricted to this actual open is ample. -/
theorem ampleOpen_isAmple : (H.baseChange (H.ampleOpen hI).ι).IsAmple := by
  apply (H.isAmple_baseChange_iff_range hI _).mpr
  rintro _ ⟨x, rfl⟩
  exact x.property

/-- The unique geometric factorization of any ample test through the ample open. -/
def ampleOpenLift (g : T ⟶ S) (ha : (H.baseChange g).IsAmple) :
    T ⟶ (H.ampleOpen hI).toScheme :=
  IsOpenImmersion.lift (H.ampleOpen hI).ι g (by
    rw [Scheme.Opens.range_ι]
    exact (H.isAmple_baseChange_iff_range hI g).mp ha)

/-- The ample lift retains the original base morphism exactly. -/
@[reassoc] theorem ampleOpenLift_inclusion (g : T ⟶ S) (ha : (H.baseChange g).IsAmple) :
    H.ampleOpenLift hI g ha ≫ (H.ampleOpen hI).ι = g :=
  IsOpenImmersion.lift_fac _ _ _

/-- The constructed open represents all ample base changes, including nonreduced tests. -/
theorem isAmple_iff_existsUnique_ampleOpenLift (g : T ⟶ S) :
    (H.baseChange g).IsAmple ↔
      ∃! v : T ⟶ (H.ampleOpen hI).toScheme, v ≫ (H.ampleOpen hI).ι = g := by
  constructor
  · intro ha
    refine ⟨H.ampleOpenLift hI g ha, H.ampleOpenLift_inclusion hI g ha, ?_⟩
    intro v hv
    apply (cancel_mono (H.ampleOpen hI).ι).mp
    exact hv.trans (H.ampleOpenLift_inclusion hI g ha).symm
  · rintro ⟨v, rfl, _⟩
    apply (H.isAmple_baseChange_iff_range hI _).mpr
    rintro _ ⟨x, rfl⟩
    exact (v x).property

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
