/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveFiberHypotheses
public import FLT.Mazur.NeronPolygonPredicate

/-!
# Smooth-or-polygon geometric fibers

The necessary nodal fiber core is strengthened by requiring each geometric fiber
to be smooth or a Néron polygon, using the cyclic pinching predicate in `Over (Spec K)`.
All existing fiber and proper-flat family conditions are retained. Arithmetic genus
one remains the separate obligation of leaf 25: these genus-free records do not yet
define the stable genus-one curves of DR II.1.4. See `docs/DR_SOURCE_LEDGER.md`.

Quantification over every geometric-point pullback square makes the full record
stable under arbitrary base change by pasting squares. The fiber structure map is
unchanged in that argument, so no base-change theorem for pinching pushouts is needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve.DRFiberClassification

open CurveFiberHypotheses

variable {K : Type u} [Field K] {X S T : Scheme.{u}}

/-- The nodal fiber core with the smooth-or-polygon condition, without a genus condition. -/
structure ClassifiedFiberCore (f : X ⟶ Spec (CommRingCat.of K)) : Prop
    extends NodalFiberCore f where
  classification : Smooth f ∨ IsNeronPolygon (Over.mk f)

/-- The strengthened fiber core on every geometric-point pullback square. -/
structure ClassifiedGeometricFibers (f : X ⟶ S) : Prop where
  fiber : ∀ (L : Type u) [Field L] [IsAlgClosed L]
    (s : Spec (CommRingCat.of L) ⟶ S) {Y : Scheme.{u}}
    (fst : Y ⟶ X) (snd : Y ⟶ Spec (CommRingCat.of L)),
    IsPullback fst snd f s → ClassifiedFiberCore snd

/-- Forgetting classification retains every necessary geometric fiber condition. -/
theorem ClassifiedGeometricFibers.toNodalGeometricFibers {f : X ⟶ S}
    (h : ClassifiedGeometricFibers f) : NodalGeometricFibers f :=
  ⟨fun L _ _ s _ fst snd hs ↦ (h.fiber L s fst snd hs).toNodalFiberCore⟩

/-- The canonical geometric fiber has the full strengthened fiber core. -/
theorem ClassifiedGeometricFibers.pullback {f : X ⟶ S}
    (h : ClassifiedGeometricFibers f) [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) : ClassifiedFiberCore (pullback.snd f s) :=
  h.fiber K s _ _ (.of_hasPullback f s)

/-- All strengthened geometric fiber conditions persist under arbitrary base change. -/
theorem ClassifiedGeometricFibers.baseChange {f : X ⟶ S}
    (h : ClassifiedGeometricFibers f) (g : T ⟶ S) :
    ClassifiedGeometricFibers (pullback.snd f g) := by
  refine ⟨fun L _ _ s Y fst snd hs ↦ ?_⟩
  exact h.fiber L (s ≫ g) (fst ≫ pullback.fst f g) snd
    (hs.paste_horiz (.of_hasPullback f g))

/-- The proper-flat family core with classified geometric fibers; genus is still absent. -/
structure ClassifiedFamilyCore (f : X ⟶ S) : Prop where
  family : ProperFlatFamily f
  fibers : ClassifiedGeometricFibers f

/-- Forgetting classification recovers the complete previous family core. -/
theorem ClassifiedFamilyCore.toNodalFamilyCore {f : X ⟶ S}
    (h : ClassifiedFamilyCore f) : NodalFamilyCore f :=
  ⟨h.family, h.fibers.toNodalGeometricFibers⟩

/-- The full genus-free family record is stable under arbitrary base change. -/
theorem ClassifiedFamilyCore.baseChange {f : X ⟶ S} (h : ClassifiedFamilyCore f)
    (g : T ⟶ S) : ClassifiedFamilyCore (pullback.snd f g) :=
  ⟨properFlatBaseChange f g h.family, h.fibers.baseChange g⟩

end FLT.Mazur.FCurve.DRFiberClassification
