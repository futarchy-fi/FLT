/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RigidifiedPicardPullbackCharts
public import FLT.Mazur.RigidifiedPicardPresheaf

/-!
# Actual rigidified pullback comparisons on test schemes

The unit and composition maps use the prescribed total-space pullback charts.
They preserve the original rigidifications, including equality transport from
composition of test-scheme maps to the named total-space map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
open FCurve.LineSheafSectionRigidity SchemePullbackSquare SheafPullbackPathComparison
variable {X S : Scheme.{u}} (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)

/-- Restriction on actual rigidified bundles over the pointed total spaces. -/
def rigidifiedBasePullback {T U : Over S} (g : T ⟶ U)
    (L : RigidifiedBundle (pointedBaseSection f e he U)) :
    RigidifiedBundle (pointedBaseSection f e he T) :=
  rigidifiedBundlePullback _ _ (relativeTotalMap f g) g.left
    (pointedBaseSection_naturality f e he g) L

/-- The comparison for identity restriction is the prescribed total-space unitor. -/
def rigidifiedBasePullbackId (T : Over S)
    (L : RigidifiedBundle (pointedBaseSection f e he T)) :
    RigidifiedIso (pointedBaseSection f e he T)
      (rigidifiedBasePullback f e he (𝟙 T) L).2 L.2 :=
  rigidifiedBundleIdentityChart _ _ _ (relativeTotalMap_id f T) rfl
    (pointedBaseSection_naturality f e he (𝟙 T)) L

/-- The comparison for two restrictions is the prescribed total-space composition chart. -/
def rigidifiedBasePullbackComp {T U V : Over S} (g : T ⟶ U) (h : U ⟶ V)
    (L : RigidifiedBundle (pointedBaseSection f e he V)) :
    RigidifiedIso (pointedBaseSection f e he T)
      (rigidifiedBasePullback f e he g (rigidifiedBasePullback f e he h L)).2
      (rigidifiedBasePullback f e he (g ≫ h) L).2 :=
  rigidifiedBundleCompositionChart _ _ _ _ _ _ _
    (pointedBaseSection_naturality f e he h) (pointedBaseSection_naturality f e he g)
    _ _ (relativeTotalMap_comp f g h).symm rfl
    (pointedBaseSection_naturality f e he (g ≫ h)) L

/-- Restriction retains the original isomorphism under sheaf pullback. -/
def rigidifiedBaseIsoPullback {T U : Over S} (g : T ⟶ U)
    {L M : RigidifiedBundle (pointedBaseSection f e he U)}
    (i : RigidifiedIso (pointedBaseSection f e he U) L.2 M.2) :
    RigidifiedIso (pointedBaseSection f e he T)
      (rigidifiedBasePullback f e he g L).2 (rigidifiedBasePullback f e he g M).2 :=
  rigidifiedIsoPullback _ _ _ _ (pointedBaseSection_naturality f e he g) i

/-- Normalizing a pulled comparison uses the original two composition charts. -/
def rigidifiedBaseIsoNormalize {T U V W : Over S} (k : T ⟶ U)
    (g : U ⟶ V) (h : U ⟶ W)
    (L : RigidifiedBundle (pointedBaseSection f e he V))
    (M : RigidifiedBundle (pointedBaseSection f e he W))
    (i : RigidifiedIso (pointedBaseSection f e he U)
      (rigidifiedBasePullback f e he g L).2 (rigidifiedBasePullback f e he h M).2) :
    RigidifiedIso (pointedBaseSection f e he T)
      (rigidifiedBasePullback f e he (k ≫ g) L).2
      (rigidifiedBasePullback f e he (k ≫ h) M).2 :=
  rigidifiedIsoTrans (rigidifiedIsoSymm (rigidifiedBasePullbackComp f e he k g L))
    (rigidifiedIsoTrans (rigidifiedBaseIsoPullback f e he k i)
      (rigidifiedBasePullbackComp f e he k h M))

/-- The normalized comparison has exactly the prescribed pullback-comparison formula. -/
theorem rigidifiedBaseIsoNormalize_val {T U V W : Over S} (k : T ⟶ U)
    (g : U ⟶ V) (h : U ⟶ W)
    (L : RigidifiedBundle (pointedBaseSection f e he V))
    (M : RigidifiedBundle (pointedBaseSection f e he W))
    (i : RigidifiedIso (pointedBaseSection f e he U)
      (rigidifiedBasePullback f e he g L).2 (rigidifiedBasePullback f e he h M).2) :
    (rigidifiedBaseIsoNormalize f e he k g h L M i).val =
      ((comparison (relativeTotalMap f k) (relativeTotalMap f g)
        (relativeTotalMap f (k ≫ g)) (relativeTotalMap_comp f k g).symm).app L.1.val).symm ≪≫
      (Scheme.Modules.pullback (relativeTotalMap f k)).mapIso i.val ≪≫
      (comparison (relativeTotalMap f k) (relativeTotalMap f h)
        (relativeTotalMap f (k ≫ h)) (relativeTotalMap_comp f k h).symm).app M.1.val := rfl

end FLT.Mazur.SchemePicard
