/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePullbackSquare

/-!
# Pasting commutative pullback paths

The comparison for two adjacent scheme squares is the composite of their
comparisons, with the original pullback composition isomorphisms at the ends.
No cartesian or finiteness hypotheses are required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackSquare
open SheafPullbackPathComparison
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {Q P X U T S : Scheme.{u}}
  (p : P ⟶ X) (q : P ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
  (w : q ≫ g = p ≫ f) (a : Q ⟶ P) (b : Q ⟶ U) (h : U ⟶ T)
  (v : b ≫ h = a ≫ q)

include w v in
/-- The pasted square commutes with its original scheme maps. -/
lemma paste_eq : b ≫ (h ≫ g) = (a ≫ p) ≫ f := by
  rw [← Category.assoc, v, Category.assoc, w, Category.assoc]

/-- Two square comparisons compose to the comparison for their pasted square. -/
@[reassoc]
theorem squareIso_paste (M : S.Modules) :
    (pullback b).map ((pullbackComp h g).hom.app M) ≫
        (squareIso f b (h ≫ g) (a ≫ p) (paste_eq p q f g w a b h v)).hom.app M =
      (squareIso q b h a v).hom.app ((pullback g).obj M) ≫
        (pullback a).map ((squareIso f q g p w).hom.app M) ≫
          (pullbackComp a p).hom.app ((pullback f).obj M) := by
  have he : (a ≫ q) ≫ g = (a ≫ p) ≫ f := by
    rw [Category.assoc, w, Category.assoc]
  have h₁ := comparison_assoc b h g (a ≫ q) (h ≫ g) ((a ≫ p) ≫ f)
    v rfl (paste_eq p q f g w a b h v) he M
  have h₂ := comparison_square f q g p w a (a ≫ q) rfl he.symm M
  have hc (c : Q ⟶ P) (d : P ⟶ T) :
      comparison c d (c ≫ d) rfl = pullbackComp c d := by
    simp [comparison, pullbackCongr]
  have hg : comparison h g (h ≫ g) rfl = pullbackComp h g := by
    simp [comparison, pullbackCongr]
  rw [hc] at h₂
  rw [hg] at h₁
  apply (cancel_mono ((pullbackComp (a ≫ p) f).hom.app M)).mp
  simp only [squareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [h₁]
  apply (cancel_epi ((comparison b h (a ≫ q) v).hom.app ((pullback g).obj M))).mpr
  apply (cancel_epi ((pullbackComp a q).hom.app ((pullback g).obj M))).mp
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  have hh := congrArg (fun k ↦ k ≫ (pullbackCongr he).hom.app M) h₂
  simpa only [squareIso, comparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    pullbackCongr, eqToIso.hom, Category.assoc, eqToHom_app,
    eqToHom_trans, eqToHom_refl,
    Category.comp_id] using hh.symm

end FLT.Mazur.SchemePullbackSquare
