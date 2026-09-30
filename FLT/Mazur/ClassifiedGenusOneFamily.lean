/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DRFiberClassification
public import FLT.Mazur.NodalGenusOneBaseChange

/-!
# Classified genus-one families

Combine the proper-flat family contract, smooth-or-polygon geometric fiber
classification and actual genus-one condition, preserving all three under base change.
The genus condition uses schemes and fields in `Type`, as does cohomology finiteness.

Sources: Deligne–Rapoport I.1.0 and II.1.4 for the family and fiber conditions;
Stacks 0BY7 for genus and 02O6 for proper coherent cohomology finiteness.
This integrates existing contracts; it does not prove polygon genus or construct
the group action required by DR II.1.12.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.FCurve

open CurveFiberHypotheses DRFiberClassification

variable {X S T : Scheme}

/-- A proper-flat family with classified geometric fibers and actual genus one. -/
structure ClassifiedGenusOneFamily (f : X ⟶ S) : Prop where
  family : ProperFlatFamily f
  classified : ClassifiedGeometricFibers f
  genus : letI : IsProper f := family.1; NodalGenusOneGeometricFibers f

/-- Forgetting genus retains the full classified family core. -/
theorem ClassifiedGenusOneFamily.toClassifiedFamilyCore {f : X ⟶ S}
    (h : ClassifiedGenusOneFamily f) : ClassifiedFamilyCore f :=
  ⟨h.family, h.classified⟩

/-- Forgetting genus and classification retains every nodal family condition. -/
theorem ClassifiedGenusOneFamily.toNodalFamilyCore {f : X ⟶ S}
    (h : ClassifiedGenusOneFamily f) : NodalFamilyCore f :=
  h.toClassifiedFamilyCore.toNodalFamilyCore

/-- All classified genus-one family conditions persist under arbitrary base change. -/
theorem ClassifiedGenusOneFamily.baseChange {f : X ⟶ S}
    (h : ClassifiedGenusOneFamily f) (g : T ⟶ S) :
    ClassifiedGenusOneFamily (pullback.snd f g) := by
  let : IsProper f := h.family.1
  exact ⟨properFlatBaseChange f g h.family, h.classified.baseChange g,
    h.genus.baseChange g⟩

end FLT.Mazur.FCurve
