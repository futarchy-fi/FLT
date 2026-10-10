/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RigidifiedPicardPresheaf
public import FLT.Mazur.LocallyNoetherianUniversalStructureSheaf

/-!
# Unique rigidified comparisons in proper families

The established universal structure-sheaf theorem makes rigidified
isomorphisms unique on every test scheme. Equality of underlying Picard
classes then produces comparisons with proved identity and cocycle laws.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
open FCurve.LineSheafSectionRigidity
variable {X S : Scheme.{0}} [IsLocallyNoetherian S]
  (f : X ⟶ S) [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]
  (e : S ⟶ X) (he : e ≫ f = 𝟙 S)

include e he in
/-- Every test scheme has the required surjectivity of actual global functions. -/
theorem pointedFamily_appTop_surjective (T : Over S) :
    Function.Surjective (Limits.pullback.snd f T.hom).appTop :=
  (LocallyNoetherianUniversalStructureSheaf.appTop_bijective
    (IsPullback.of_hasPullback f T.hom) e he).surjective

/-- Rigidified comparisons are unique after arbitrary change of the base. -/
theorem pointedFamily_rigidifiedIso_subsingleton (T : Over S)
    (L M : RigidifiedBundle (pointedBaseSection f e he T)) :
    Subsingleton (RigidifiedIso (pointedBaseSection f e he T) L.2 M.2) :=
  rigidifiedIso_subsingleton (Limits.pullback.snd f T.hom) _
    (pointedBaseSection_snd f e he T) (pointedFamily_appTop_surjective f e he T)
    L.1.property L.2 M.2

/-- Equality of underlying classes has a unique comparison preserving rigidifications. -/
theorem pointedFamily_existsUnique_iso (T : Over S)
    (L M : RigidifiedBundle (pointedBaseSection f e he T))
    (h : mk L.1.val L.1.property = mk M.1.val M.1.property) :
    ∃! i : L.1.val ≅ M.1.val,
      (Scheme.Modules.pullback (pointedBaseSection f e he T)).map i.hom ≫ M.2.hom =
        L.2.hom := by
  obtain ⟨i⟩ := (mk_eq_mk_iff L.1.property M.1.property).mp h
  exact existsUnique_rigidifiedIso (Limits.pullback.snd f T.hom) _
    (pointedBaseSection_snd f e he T) L.1.property
    (pointedFamily_appTop_surjective f e he T) L.2 M.2 i

/-- The comparison obtained from equality of the original Picard representatives. -/
def pointedFamilyClassIso (T : Over S)
    (L M : RigidifiedBundle (pointedBaseSection f e he T))
    (h : mk L.1.val L.1.property = mk M.1.val M.1.property) : L.1.val ≅ M.1.val :=
  (pointedFamily_existsUnique_iso f e he T L M h).exists.choose

/-- The chosen comparison preserves the specified original rigidifications. -/
theorem pointedFamilyClassIso_preserves (T : Over S)
    (L M : RigidifiedBundle (pointedBaseSection f e he T))
    (h : mk L.1.val L.1.property = mk M.1.val M.1.property) :
    (Scheme.Modules.pullback (pointedBaseSection f e he T)).map
      (pointedFamilyClassIso f e he T L M h).hom ≫ M.2.hom = L.2.hom :=
  (pointedFamily_existsUnique_iso f e he T L M h).exists.choose_spec

/-- Any rigidification-preserving comparison is the one obtained from class equality. -/
theorem pointedFamilyClassIso_unique (T : Over S)
    (L M : RigidifiedBundle (pointedBaseSection f e he T))
    (h : mk L.1.val L.1.property = mk M.1.val M.1.property)
    (i : L.1.val ≅ M.1.val)
    (hi : (Scheme.Modules.pullback (pointedBaseSection f e he T)).map i.hom ≫
      M.2.hom = L.2.hom) : i = pointedFamilyClassIso f e he T L M h := by
  exact (pointedFamily_existsUnique_iso f e he T L M h).unique hi
    (pointedFamilyClassIso_preserves f e he T L M h)

/-- The comparison of a rigidified representative with itself is the identity. -/
theorem pointedFamilyClassIso_refl (T : Over S)
    (L : RigidifiedBundle (pointedBaseSection f e he T)) :
    pointedFamilyClassIso f e he T L L rfl = Iso.refl L.1.val := by
  symm
  apply pointedFamilyClassIso_unique
  simp

/-- Comparisons from equal classes satisfy the actual isomorphism cocycle equation. -/
theorem pointedFamilyClassIso_trans (T : Over S)
    (L M N : RigidifiedBundle (pointedBaseSection f e he T))
    (h : mk L.1.val L.1.property = mk M.1.val M.1.property)
    (k : mk M.1.val M.1.property = mk N.1.val N.1.property) :
    pointedFamilyClassIso f e he T L M h ≪≫ pointedFamilyClassIso f e he T M N k =
      pointedFamilyClassIso f e he T L N (h.trans k) := by
  apply pointedFamilyClassIso_unique
  simp only [Iso.trans_hom, Functor.map_comp, Category.assoc,
    pointedFamilyClassIso_preserves]

/-- The unique class comparison pulls back as the original total-space isomorphism. -/
theorem pointedFamilyClassIso_pullback {T U : Over S} (g : T ⟶ U)
    (L M : RigidifiedBundle (pointedBaseSection f e he U))
    (h : mk L.1.val L.1.property = mk M.1.val M.1.property) :
    (Scheme.Modules.pullback (relativeTotalMap f g)).mapIso
        (pointedFamilyClassIso f e he U L M h) =
      pointedFamilyClassIso f e he T
        (rigidifiedBundlePullback _ _ (relativeTotalMap f g) g.left
          (pointedBaseSection_naturality f e he g) L)
        (rigidifiedBundlePullback _ _ (relativeTotalMap f g) g.left
          (pointedBaseSection_naturality f e he g) M)
        (congrArg (pullback (relativeTotalMap f g)) h) := by
  refine pointedFamilyClassIso_unique f e he T
    (rigidifiedBundlePullback _ _ (relativeTotalMap f g) g.left
      (pointedBaseSection_naturality f e he g) L)
    (rigidifiedBundlePullback _ _ (relativeTotalMap f g) g.left
      (pointedBaseSection_naturality f e he g) M)
    (congrArg (pullback (relativeTotalMap f g)) h) _ ?_
  exact (rigidifiedIsoPullback _ _ (relativeTotalMap f g) g.left
    (pointedBaseSection_naturality f e he g)
    (⟨pointedFamilyClassIso f e he U L M h,
      pointedFamilyClassIso_preserves f e he U L M h⟩ :
      RigidifiedIso (pointedBaseSection f e he U) L.2 M.2)).property

end FLT.Mazur.SchemePicard
