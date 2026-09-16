/-
Copyright (c) 2026 FLT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT contributors
-/
module

public import FLT.Deformations.DeSmitLenstra.FramedUniversalProperty
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

/-!
# Finite residual quotients of a profinite group

For a continuous residual representation of a profinite group, this file organizes the finite
quotients through which the residual representation factors. The reverse-inclusion order gives
the orientation needed for the inverse system of completed framed representation rings.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace Deformation

noncomputable section

variable (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
variable (n : Type u) [Fintype n] [DecidableEq n]
variable [Finite (ResidueField O)]
variable (rho : G →ₜ* GL n (ProartinianCat.residueField (𝓞 := O)))

/-- The open normal kernel of a continuous residual representation. -/
def residualOpenKernel : OpenNormalSubgroup G where
  toSubgroup := rho.toMonoidHom.ker
  isOpen' := MonoidHom.continuous_iff_isOpen_ker.mp rho.continuous

/-- Open normal subgroups contained in the residual kernel, ordered by reverse inclusion. -/
abbrev ResidualQuotientIndex : Type u :=
  OrderDual { U : OpenNormalSubgroup G // U ≤ residualOpenKernel O G n rho }

namespace ResidualQuotientIndex

/-- The residual kernel itself gives a finite quotient index. -/
def kernelIndex : ResidualQuotientIndex O G n rho :=
  OrderDual.toDual ⟨residualOpenKernel O G n rho, le_rfl⟩

instance : Nonempty (ResidualQuotientIndex O G n rho) :=
  ⟨kernelIndex O G n rho⟩

/-- The open normal subgroup represented by an index. -/
def subgroup (U : ResidualQuotientIndex O G n rho) : OpenNormalSubgroup G :=
  (OrderDual.ofDual U).1

/-- The common refinement of two residual finite quotients. -/
def commonRefinement (U V : ResidualQuotientIndex O G n rho) :
    ResidualQuotientIndex O G n rho :=
  OrderDual.toDual ⟨subgroup O G n rho U ⊓ subgroup O G n rho V,
    inf_le_left.trans (OrderDual.ofDual U).2⟩

omit [IsNoetherianRing O] [CompactSpace G] [TotallyDisconnectedSpace G]
  [Finite (ResidueField O)] in
lemma le_commonRefinement_left (U V : ResidualQuotientIndex O G n rho) :
    U ≤ commonRefinement O G n rho U V := by
  change subgroup O G n rho U ⊓ subgroup O G n rho V ≤ subgroup O G n rho U
  exact inf_le_left

omit [IsNoetherianRing O] [CompactSpace G] [TotallyDisconnectedSpace G]
  [Finite (ResidueField O)] in
lemma le_commonRefinement_right (U V : ResidualQuotientIndex O G n rho) :
    V ≤ commonRefinement O G n rho U V := by
  change subgroup O G n rho U ⊓ subgroup O G n rho V ≤ subgroup O G n rho V
  exact inf_le_right

omit [IsNoetherianRing O] [CompactSpace G] [TotallyDisconnectedSpace G]
  [Finite (ResidueField O)] in
/-- Residual finite quotients are directed under refinement. -/
lemma directed : Directed (· ≤ ·)
    (id : ResidualQuotientIndex O G n rho → ResidualQuotientIndex O G n rho) := fun U V ↦
  ⟨commonRefinement O G n rho U V,
    le_commonRefinement_left O G n rho U V,
    le_commonRefinement_right O G n rho U V⟩

/-- The finite quotient group represented by an index. -/
abbrev Quotient (U : ResidualQuotientIndex O G n rho) :=
  G ⧸ (subgroup O G n rho U).toSubgroup

instance (U : ResidualQuotientIndex O G n rho) : Finite (Quotient O G n rho U) :=
  inferInstance

/-- The residual representation descended to a finite quotient. -/
def representation (U : ResidualQuotientIndex O G n rho) :
    Quotient O G n rho U →* GL n (ResidueField O) :=
  QuotientGroup.lift (subgroup O G n rho U).toSubgroup rho.toMonoidHom
    (OrderDual.ofDual U).2

omit [IsNoetherianRing O] [CompactSpace G] [TotallyDisconnectedSpace G]
  [Finite (ResidueField O)] in
@[simp]
lemma representation_mk (U : ResidualQuotientIndex O G n rho) (g : G) :
    representation O G n rho U (QuotientGroup.mk g) = rho g :=
  QuotientGroup.lift_mk _ _ g

/-- The quotient map associated to an inequality of residual quotient indices. -/
def quotientMap {U V : ResidualQuotientIndex O G n rho} (h : U ≤ V) :
    Quotient O G n rho V →* Quotient O G n rho U :=
  QuotientGroup.map (subgroup O G n rho V).toSubgroup
    (subgroup O G n rho U).toSubgroup
    (MonoidHom.id G) h

omit [IsNoetherianRing O] [CompactSpace G] [TotallyDisconnectedSpace G]
  [Finite (ResidueField O)] in
@[simp]
lemma quotientMap_mk {U V : ResidualQuotientIndex O G n rho} (h : U ≤ V) (g : G) :
    quotientMap O G n rho h (QuotientGroup.mk g) = QuotientGroup.mk g :=
  rfl

omit [IsNoetherianRing O] [CompactSpace G] [TotallyDisconnectedSpace G]
  [Finite (ResidueField O)] in
lemma representation_comp_quotientMap
    {U V : ResidualQuotientIndex O G n rho} (h : U ≤ V) :
    (representation O G n rho U).comp (quotientMap O G n rho h) =
      representation O G n rho V := by
  apply (MonoidHom.cancel_right
    (QuotientGroup.mk'_surjective (subgroup O G n rho V).toSubgroup)).mp
  ext g
  simp

omit [IsNoetherianRing O] [CompactSpace G] [TotallyDisconnectedSpace G]
  [Finite (ResidueField O)] in
@[simp]
lemma quotientMap_refl (U : ResidualQuotientIndex O G n rho) :
    quotientMap O G n rho (le_refl U) = MonoidHom.id (Quotient O G n rho U) := by
  apply (MonoidHom.cancel_right
    (QuotientGroup.mk'_surjective (subgroup O G n rho U).toSubgroup)).mp
  ext g
  rfl

omit [IsNoetherianRing O] [CompactSpace G] [TotallyDisconnectedSpace G]
  [Finite (ResidueField O)] in
lemma quotientMap_comp {U V W : ResidualQuotientIndex O G n rho}
    (hUV : U ≤ V) (hVW : V ≤ W) :
    (quotientMap O G n rho hUV).comp (quotientMap O G n rho hVW) =
      quotientMap O G n rho (hUV.trans hVW) := by
  apply (MonoidHom.cancel_right
    (QuotientGroup.mk'_surjective (subgroup O G n rho W).toSubgroup)).mp
  ext g
  rfl

/-- Pull the universal lift at `U` back along a finer finite quotient `V`. -/
def transitionLift {U V : ResidualQuotientIndex O G n rho} (h : U ≤ V) :
    Quotient O G n rho V →* GL n
      (framedCompletionObject O (Quotient O G n rho U) n
        (representation O G n rho U)) :=
  (universalFramedLift O (Quotient O G n rho U) n
    (representation O G n rho U)).comp (quotientMap O G n rho h)

omit [TotallyDisconnectedSpace G] in
lemma transitionLift_isFramedLift
    {U V : ResidualQuotientIndex O G n rho} (h : U ≤ V) :
    IsFramedLift O (Quotient O G n rho V) n (representation O G n rho V)
      (framedCompletionObject O (Quotient O G n rho U) n
        (representation O G n rho U))
      (transitionLift O G n rho h) := by
  ext g i j
  change (ProartinianCat.toResidueField
      (framedCompletionObject O (Quotient O G n rho U) n
        (representation O G n rho U))).hom
      (framedRepresentationToCompletion O (Quotient O G n rho U) n
        (representation O G n rho U)
        (framedRepresentationQuotient O (Quotient O G n rho U) n
          (MvPolynomial.X (QuotientGroup.mk g, (i, j))))) =
    representation O G n rho V (QuotientGroup.mk g) i j
  rw [framedCompletion_toResidue_apply, representation_mk]
  simp [residualRepresentationHom, FramedRepresentationRing.ofRepresentation,
    framedRepresentationQuotient]

/-- The transition map between finite-quotient completed framed rings. -/
def transitionMap {U V : ResidualQuotientIndex O G n rho} (h : U ≤ V) :
    framedCompletionObject O (Quotient O G n rho V) n
        (representation O G n rho V) ⟶
      framedCompletionObject O (Quotient O G n rho U) n
        (representation O G n rho U) :=
  framedCompletionLiftToHom O (Quotient O G n rho V) n
    (representation O G n rho V)
    (framedCompletionObject O (Quotient O G n rho U) n
      (representation O G n rho U))
    ⟨transitionLift O G n rho h, transitionLift_isFramedLift O G n rho h⟩

omit [TotallyDisconnectedSpace G] in
lemma transitionMap_universalFramedLift
    {U V : ResidualQuotientIndex O G n rho} (h : U ≤ V) :
    (Matrix.GeneralLinearGroup.map (transitionMap O G n rho h).hom.toRingHom).comp
        (universalFramedLift O (Quotient O G n rho V) n
          (representation O G n rho V)) =
      transitionLift O G n rho h :=
  framedCompletionMap_universalFramedLift O (Quotient O G n rho V) n
    (representation O G n rho V)
    (framedCompletionObject O (Quotient O G n rho U) n
      (representation O G n rho U)) _ _

omit [TotallyDisconnectedSpace G] in
lemma transitionMap_universalFramedLift_apply
    {U V : ResidualQuotientIndex O G n rho} (h : U ≤ V)
    (x : Quotient O G n rho V) (i j : n) :
    (transitionMap O G n rho h).hom
        (framedRepresentationToCompletionObject O (Quotient O G n rho V) n
          (representation O G n rho V)
          (framedRepresentationQuotient O (Quotient O G n rho V) n
            (MvPolynomial.X (x, (i, j))))) =
      framedRepresentationToCompletionObject O (Quotient O G n rho U) n
        (representation O G n rho U)
        (framedRepresentationQuotient O (Quotient O G n rho U) n
          (MvPolynomial.X (quotientMap O G n rho h x, (i, j)))) := by
  have hx := congrArg
    (fun r : Quotient O G n rho V →* GL n
        (framedCompletionObject O (Quotient O G n rho U) n
          (representation O G n rho U)) ↦
      (r x).1 i j)
    (transitionMap_universalFramedLift O G n rho h)
  change _ = _ at hx
  exact hx

omit [TotallyDisconnectedSpace G] in
@[simp]
lemma transitionMap_refl (U : ResidualQuotientIndex O G n rho) :
    transitionMap O G n rho (le_refl U) =
      𝟙 (framedCompletionObject O (Quotient O G n rho U) n
        (representation O G n rho U)) := by
  symm
  apply framedCompletionHom_unique O (Quotient O G n rho U) n
    (representation O G n rho U)
    (framedCompletionObject O (Quotient O G n rho U) n
      (representation O G n rho U))
    (transitionLift O G n rho (le_refl U))
    (transitionLift_isFramedLift O G n rho (le_refl U)) (𝟙 _)
  ext g i j
  rfl

omit [TotallyDisconnectedSpace G] in
lemma transitionMap_comp {U V W : ResidualQuotientIndex O G n rho}
    (hUV : U ≤ V) (hVW : V ≤ W) :
    transitionMap O G n rho hVW ≫ transitionMap O G n rho hUV =
      transitionMap O G n rho (hUV.trans hVW) := by
  apply framedCompletionHom_unique O (Quotient O G n rho W) n
    (representation O G n rho W)
    (framedCompletionObject O (Quotient O G n rho U) n
      (representation O G n rho U))
    (transitionLift O G n rho (hUV.trans hVW))
    (transitionLift_isFramedLift O G n rho (hUV.trans hVW))
  ext g i j
  change (transitionMap O G n rho hUV).hom
      ((transitionMap O G n rho hVW).hom
        (framedRepresentationToCompletionObject O (Quotient O G n rho W) n
          (representation O G n rho W)
          (framedRepresentationQuotient O (Quotient O G n rho W) n
            (MvPolynomial.X (QuotientGroup.mk g, (i, j)))))) =
    framedRepresentationToCompletionObject O (Quotient O G n rho U) n
      (representation O G n rho U)
      (framedRepresentationQuotient O (Quotient O G n rho U) n
        (MvPolynomial.X (QuotientGroup.mk g, (i, j))))
  rw [transitionMap_universalFramedLift_apply,
    transitionMap_universalFramedLift_apply, quotientMap_mk, quotientMap_mk]

/-- The underlying finite-level completed framed ring. -/
abbrev Completion (U : ResidualQuotientIndex O G n rho) :=
  framedCompletionObject O (Quotient O G n rho U) n
    (representation O G n rho U)

/-- The ring-homomorphism inverse system underlying the finite-level completion maps. -/
def transitionRingHom (U V : ResidualQuotientIndex O G n rho) (h : U ≤ V) :
    Completion O G n rho V →+* Completion O G n rho U :=
  (transitionMap O G n rho h).hom.toRingHom

omit [TotallyDisconnectedSpace G] in
@[simp]
lemma transitionRingHom_refl (U : ResidualQuotientIndex O G n rho) :
    transitionRingHom O G n rho U U (le_refl U) = RingHom.id _ := by
  rw [transitionRingHom, transitionMap_refl]
  rfl

omit [TotallyDisconnectedSpace G] in
lemma transitionRingHom_comp {U V W : ResidualQuotientIndex O G n rho}
    (hUV : U ≤ V) (hVW : V ≤ W) :
    (transitionRingHom O G n rho U V hUV).comp
        (transitionRingHom O G n rho V W hVW) =
      transitionRingHom O G n rho U W (hUV.trans hVW) := by
  exact congrArg (fun f : Completion O G n rho W ⟶ Completion O G n rho U ↦
    f.hom.toRingHom) (transitionMap_comp O G n rho hUV hVW)

end ResidualQuotientIndex

end

end Deformation
