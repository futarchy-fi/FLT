/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyRigidifiedNamedTransitions
public import FLT.Mazur.SchemeIndependentCanonicalOverlap

/-!
# Compatibility of rigidified comparisons on a common base chart

Uniqueness of rigidified isomorphisms identifies the normalized restrictions of
any two local comparisons. The original canonical overlap equation follows.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
open FCurve.LineSheafSectionRigidity SheafPullbackPathComparison
variable {X S : Scheme.{0}} (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
  [IsLocallyNoetherian S] [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]
  {T U V W : Over S} (k : T ⟶ U) (l : T ⟶ V) (g : U ⟶ W) (h : V ⟶ W)
  (v : T ⟶ W) (wk : k ≫ g = v) (wl : l ≫ h = v)
  (L M : RigidifiedBundle (pointedBaseSection f e he W))
  (a : RigidifiedIso (pointedBaseSection f e he U)
    (rigidifiedBasePullback f e he g L).2 (rigidifiedBasePullback f e he g M).2)
  (b : RigidifiedIso (pointedBaseSection f e he V)
    (rigidifiedBasePullback f e he h L).2 (rigidifiedBasePullback f e he h M).2)

/-- Any two rigidified comparisons agree after normalization to the same base chart. -/
theorem rigidifiedComparisons_normalized :
    SchemeIndependentPairNormalization.normalize
      (relativeTotalMap f g) (relativeTotalMap f g) (relativeTotalMap f k)
      (relativeTotalMap f v) (relativeTotalMap f v)
      ((relativeTotalMap_comp f k g).symm.trans (congrArg (relativeTotalMap f) wk))
      ((relativeTotalMap_comp f k g).symm.trans (congrArg (relativeTotalMap f) wk))
      L.1.val M.1.val a.val =
    SchemeIndependentPairNormalization.normalize
      (relativeTotalMap f h) (relativeTotalMap f h) (relativeTotalMap f l)
      (relativeTotalMap f v) (relativeTotalMap f v)
      ((relativeTotalMap_comp f l h).symm.trans (congrArg (relativeTotalMap f) wl))
      ((relativeTotalMap_comp f l h).symm.trans (congrArg (relativeTotalMap f) wl))
      L.1.val M.1.val b.val := by
  rw [← rigidifiedBaseIsoNormalizeNamed_val f e he k g g v v wk wk L M a,
    ← rigidifiedBaseIsoNormalizeNamed_val f e he l h h v v wl wl L M b]
  exact congrArg Subtype.val
    ((pointedFamily_rigidifiedIso_subsingleton f e he T
      (rigidifiedBasePullback f e he v L) (rigidifiedBasePullback f e he v M)).elim _ _)

/-- The original local comparisons intertwine the canonical common-chart overlaps. -/
theorem rigidifiedComparisons_overlap :
    (SchemeIndependentCanonicalOverlap.overlap
      (relativeTotalMap f g) (relativeTotalMap f h)
      (relativeTotalMap f k) (relativeTotalMap f l) (relativeTotalMap f v)
      ((relativeTotalMap_comp f k g).symm.trans (congrArg (relativeTotalMap f) wk))
      ((relativeTotalMap_comp f l h).symm.trans (congrArg (relativeTotalMap f) wl))
      L.1.val).hom ≫ (Scheme.Modules.pullback (relativeTotalMap f l)).map b.val.hom =
    (Scheme.Modules.pullback (relativeTotalMap f k)).map a.val.hom ≫
      (SchemeIndependentCanonicalOverlap.overlap
        (relativeTotalMap f g) (relativeTotalMap f h)
        (relativeTotalMap f k) (relativeTotalMap f l) (relativeTotalMap f v)
        ((relativeTotalMap_comp f k g).symm.trans (congrArg (relativeTotalMap f) wk))
        ((relativeTotalMap_comp f l h).symm.trans (congrArg (relativeTotalMap f) wl))
        M.1.val).hom := by
  have hh := congrArg Iso.hom (rigidifiedComparisons_normalized
    f e he k l g h v wk wl L M a b).symm
  apply (cancel_epi ((comparison (relativeTotalMap f k) (relativeTotalMap f g)
    (relativeTotalMap f v)
    ((relativeTotalMap_comp f k g).symm.trans
      (congrArg (relativeTotalMap f) wk))).inv.app L.1.val)).mp
  apply (cancel_mono ((comparison (relativeTotalMap f l) (relativeTotalMap f h)
    (relativeTotalMap f v)
    ((relativeTotalMap_comp f l h).symm.trans
      (congrArg (relativeTotalMap f) wl))).hom.app M.1.val)).mp
  simpa only [SchemeIndependentCanonicalOverlap.overlap,
    SchemeIndependentPairNormalization.normalize, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id] using hh

end FLT.Mazur.SchemePicard
