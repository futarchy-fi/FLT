/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOpenImmersionGluing
public import FLT.Mazur.SheafPullbackPathComparison

/-!
# Detecting morphisms on affine tests of two source covers

Pull back each source open cover, then take affine covers. These tests
jointly detect equations between module sheaf morphisms on the test scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u v w
namespace FLT.Mazur.ModuleSheafOpenImmersionGluing
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Equality after a composite pullback implies equality after the iterated pullback. -/
lemma map_map_eq_of_composite {T U X : Scheme.{u}} (t : T ⟶ U) (b : U ⟶ X)
    {M N : X.Modules} (a a' : M ⟶ N)
    (h : (pullback (t ≫ b)).map a = (pullback (t ≫ b)).map a') :
    (pullback t).map ((pullback b).map a) = (pullback t).map ((pullback b).map a') := by
  apply (cancel_mono ((comparison t b (t ≫ b) rfl).hom.app N)).mp
  change (pullback b ⋙ pullback t).map a ≫ _ =
    (pullback b ⋙ pullback t).map a' ≫ _
  rw [(comparison t b (t ≫ b) rfl).hom.naturality,
    (comparison t b (t ≫ b) rfl).hom.naturality, h]

/-- Affine tests lifting to both source open covers detect sheaf morphism equations. -/
lemma hom_ext_of_affine_pair_tests {Z Y W : Scheme.{u}}
    (U : Y.OpenCover.{v}) (V : W.OpenCover.{w}) (d : Z ⟶ Y) (e : Z ⟶ W)
    {M N : Z.Modules} (a b : M ⟶ N)
    (h : ∀ i j {A : CommRingCat.{u}} (t : Spec A ⟶ Z)
      (l : Spec A ⟶ U.X i) (r : Spec A ⟶ V.X j),
      l ≫ U.f i = t ≫ d → r ≫ V.f j = t ≫ e →
      (pullback t).map a = (pullback t).map b) : a = b := by
  let P : Z.OpenCover := U.pullback₁ d
  apply hom_ext P.X P.f (fun z ↦ ⟨P.idx z, P.covers z⟩)
  intro i
  let Q : (P.X i).OpenCover := V.pullback₁ (P.f i ≫ e)
  apply hom_ext Q.X Q.f (fun z ↦ ⟨Q.idx z, Q.covers z⟩)
  intro j
  let R := (Q.X j).affineOpenCover
  apply hom_ext (fun k ↦ Spec (R.X k)) R.f (fun z ↦ ⟨R.idx z, R.covers z⟩)
  intro k
  apply map_map_eq_of_composite (R.f k) (Q.f j)
  apply map_map_eq_of_composite (R.f k ≫ Q.f j) (P.f i)
  apply h i j ((R.f k ≫ Q.f j) ≫ P.f i)
    ((R.f k ≫ Q.f j) ≫ U.pullbackHom d i)
    (R.f k ≫ V.pullbackHom (P.f i ≫ e) j)
  · simp only [P, Q, Category.assoc, Scheme.Cover.pullbackHom_map]
  · simp only [P, Q, Category.assoc, Scheme.Cover.pullbackHom_map]

end FLT.Mazur.ModuleSheafOpenImmersionGluing
