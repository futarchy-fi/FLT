/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RigidifiedPicardPullbackCoherence
public import FLT.Mazur.SchemePullbackCompositeCharts

/-!
# Rigidified pullback charts with named endpoints

Equality transport to separately named identity and composite maps retains
rigidification. Inverses and composites of preserving isomorphisms do as well.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
open FCurve FCurve.LineSheafSectionRigidity SchemePullbackSquare
open SheafPullbackPathComparison
variable {X Y Z S T U : Scheme.{u}}

/-- Inverting an actual preserving isomorphism preserves the rigidifications. -/
def rigidifiedIsoSymm {s : S ⟶ X} {L M : RigidifiedBundle s}
    (i : RigidifiedIso s L.2 M.2) : RigidifiedIso s M.2 L.2 := by
  refine ⟨i.val.symm, ?_⟩
  simp only [Iso.symm_hom]
  apply (cancel_epi ((Scheme.Modules.pullback s).map i.val.hom)).mp
  rw [← Category.assoc, ← Functor.map_comp, i.val.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, i.property]

/-- Composing original preserving isomorphisms preserves rigidifications. -/
def rigidifiedIsoTrans {s : S ⟶ X} {L M N : RigidifiedBundle s}
    (i : RigidifiedIso s L.2 M.2) (j : RigidifiedIso s M.2 N.2) :
    RigidifiedIso s L.2 N.2 :=
  ⟨i.val ≪≫ j.val, by
    simp only [Iso.trans_hom, Functor.map_comp, Category.assoc, j.property, i.property]⟩

/-- The identity chart includes equality transport of the specified maps. -/
def rigidifiedBundleIdentityChart (s : S ⟶ X) (p : X ⟶ X) (b : S ⟶ S)
    (hp : p = 𝟙 X) (hb : b = 𝟙 S) (w : s ≫ p = b ≫ s)
    (L : RigidifiedBundle s) :
    RigidifiedIso s (rigidifiedBundlePullback s s p b w L).2 L.2 := by
  refine ⟨(identityIso p hp).app L.1.val, ?_⟩
  subst p b
  exact rigidifiedBundlePullback_id_preserves s L

/-- Composite charts include equality transport to the prescribed composite endpoints. -/
def rigidifiedBundleCompositionChart (s : S ⟶ X) (t : T ⟶ Y) (r : U ⟶ Z)
    (p : Y ⟶ X) (b : T ⟶ S) (q : Z ⟶ Y) (c : U ⟶ T)
    (w : t ≫ p = b ≫ s) (v : r ≫ q = c ≫ t)
    (qp : Z ⟶ X) (cb : U ⟶ S) (hp : q ≫ p = qp) (hb : c ≫ b = cb)
    (wv : r ≫ qp = cb ≫ s) (L : RigidifiedBundle s) :
    RigidifiedIso r
      (rigidifiedBundlePullback t r q c v (rigidifiedBundlePullback s t p b w L)).2
      (rigidifiedBundlePullback s r qp cb wv L).2 := by
  refine ⟨(comparison q p qp hp).app L.1.val, ?_⟩
  subst qp cb
  exact rigidifiedBundlePullback_comp_preserves s t r p b q c w v L

end FLT.Mazur.SchemePicard
