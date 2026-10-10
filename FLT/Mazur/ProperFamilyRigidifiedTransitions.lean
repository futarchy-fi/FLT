/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RigidifiedPicardBaseCharts
public import FLT.Mazur.ProperFamilyRigidifiedComparisons

/-!
# Transitions between rigidified local representatives

Equality of restricted classes supplies unique actual transitions. Their
normalization along further restriction is the prescribed pullback formula,
and identity and cocycle laws hold on the original sheaf isomorphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
open FCurve.LineSheafSectionRigidity
variable {X S : Scheme.{0}}
  (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)

/-- The underlying Picard class of an actually restricted representative. -/
def rigidifiedBaseClass {T U : Over S} (g : T ⟶ U)
    (L : RigidifiedBundle (pointedBaseSection f e he U)) :
    Pic (Limits.pullback f T.hom) :=
  pullback (relativeTotalMap f g) (mk L.1.val L.1.property)

/-- Further restriction of a representative class is restriction along the composite. -/
theorem rigidifiedBaseClass_comp {T U V : Over S} (k : T ⟶ U) (g : U ⟶ V)
    (L : RigidifiedBundle (pointedBaseSection f e he V)) :
    pullback (relativeTotalMap f k) (rigidifiedBaseClass f e he g L) =
      rigidifiedBaseClass f e he (k ≫ g) L := by
  simp only [rigidifiedBaseClass, relativeTotalMap_comp, pullback_comp]

variable [IsLocallyNoetherian S] [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]

/-- The unique transition between original bundles with equal restricted classes. -/
def rigidifiedTransition {T U V : Over S} (g : T ⟶ U) (h : T ⟶ V)
    (L : RigidifiedBundle (pointedBaseSection f e he U))
    (M : RigidifiedBundle (pointedBaseSection f e he V))
    (a : rigidifiedBaseClass f e he g L = rigidifiedBaseClass f e he h M) :
    RigidifiedIso (pointedBaseSection f e he T)
      (rigidifiedBasePullback f e he g L).2 (rigidifiedBasePullback f e he h M).2 :=
  ⟨pointedFamilyClassIso f e he T _ _ a, pointedFamilyClassIso_preserves f e he T
    (rigidifiedBasePullback f e he g L) (rigidifiedBasePullback f e he h M) a⟩

/-- The transition on an identical representative is its actual identity isomorphism. -/
theorem rigidifiedTransition_refl {T U : Over S} (g : T ⟶ U)
    (L : RigidifiedBundle (pointedBaseSection f e he U)) :
    (rigidifiedTransition f e he g g L L rfl).val =
      Iso.refl (rigidifiedBasePullback f e he g L).1.val :=
  pointedFamilyClassIso_refl f e he T _

/-- Three compatible restricted classes give the actual transition cocycle. -/
theorem rigidifiedTransition_trans {T U V W : Over S}
    (g : T ⟶ U) (h : T ⟶ V) (k : T ⟶ W)
    (L : RigidifiedBundle (pointedBaseSection f e he U))
    (M : RigidifiedBundle (pointedBaseSection f e he V))
    (N : RigidifiedBundle (pointedBaseSection f e he W))
    (a : rigidifiedBaseClass f e he g L = rigidifiedBaseClass f e he h M)
    (b : rigidifiedBaseClass f e he h M = rigidifiedBaseClass f e he k N) :
    (rigidifiedTransition f e he g h L M a).val ≪≫
        (rigidifiedTransition f e he h k M N b).val =
      (rigidifiedTransition f e he g k L N (a.trans b)).val :=
  pointedFamilyClassIso_trans f e he T (rigidifiedBasePullback f e he g L)
    (rigidifiedBasePullback f e he h M) (rigidifiedBasePullback f e he k N) a b

omit [IsLocallyNoetherian S] [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f] in
/-- Class compatibility remains true after a further test-scheme restriction. -/
theorem rigidifiedTransition_class_pullback {T U V W : Over S}
    (k : T ⟶ U) (g : U ⟶ V) (h : U ⟶ W)
    (L : RigidifiedBundle (pointedBaseSection f e he V))
    (M : RigidifiedBundle (pointedBaseSection f e he W))
    (a : rigidifiedBaseClass f e he g L = rigidifiedBaseClass f e he h M) :
    rigidifiedBaseClass f e he (k ≫ g) L = rigidifiedBaseClass f e he (k ≫ h) M := by
  rw [← rigidifiedBaseClass_comp, ← rigidifiedBaseClass_comp, a]

/-- Normalizing the pulled original transition gives precisely the further transition. -/
theorem rigidifiedTransition_normalize {T U V W : Over S}
    (k : T ⟶ U) (g : U ⟶ V) (h : U ⟶ W)
    (L : RigidifiedBundle (pointedBaseSection f e he V))
    (M : RigidifiedBundle (pointedBaseSection f e he W))
    (a : rigidifiedBaseClass f e he g L = rigidifiedBaseClass f e he h M) :
    rigidifiedBaseIsoNormalize f e he k g h L M (rigidifiedTransition f e he g h L M a) =
      rigidifiedTransition f e he (k ≫ g) (k ≫ h) L M
        (rigidifiedTransition_class_pullback f e he k g h L M a) :=
  (pointedFamily_rigidifiedIso_subsingleton f e he T _ _).elim _ _

end FLT.Mazur.SchemePicard
