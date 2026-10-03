/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineFieldExtension
public import FLT.Mazur.OverPullbackCoproduct
public import FLT.Mazur.PolygonPinchingAffineBaseChange

/-!
# Field extension of the specified polygon diagram

The projective-line endpoint comparisons and finite coproduct preservation
identify the base-changed pinching span with the specified span over the new
field. Its pushout presents every chosen geometric pullback square.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.PolygonFieldExtension
open PolygonPinching ProjectiveLineFieldExtension
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
local notation "F" => Over.pullback (ProjectiveLineProductCharts.parameterToBase K L)

/-- Extend a finite family and its chosen coefficient-change isomorphisms. -/
def coproductIso {ι : Type} [Finite ι] (X : ι → Over (Spec (.of K)))
    (Y : ι → Over (Spec (.of L))) (e : ∀ i, Y i ≅ (F).obj (X i)) :
    (∐ Y) ≅ (F).obj (∐ X) :=
  Sigma.mapIso e ≪≫ OverPullbackCoproduct.equivalence _ X

@[reassoc (attr := simp)] theorem inclusion {ι : Type} [Finite ι]
    (X : ι → Over (Spec (.of K))) (Y : ι → Over (Spec (.of L)))
    (e : ∀ i, Y i ≅ (F).obj (X i)) (i : ι) :
    Sigma.ι Y i ≫ (coproductIso K L X Y e).hom =
      (e i).hom ≫ (F).map (Sigma.ι X i) := by
  simp [coproductIso]

/-- The normalization components after coefficient change. -/
def componentsIso (n : ℕ) : components L n ≅ (F).obj (components K n) :=
  coproductIso K L _ _ (fun _ ↦ componentIso K L)
/-- The two branches of every node after coefficient change. -/
def branchesIso (n : ℕ) : branches L n ≅ (F).obj (branches K n) :=
  coproductIso K L _ _ (fun _ ↦ pointIso K L)
/-- The node points after coefficient change. -/
def nodesIso (n : ℕ) : nodes L n ≅ (F).obj (nodes K n) :=
  coproductIso K L _ _ (fun _ ↦ pointIso K L)

@[reassoc] theorem toComponents_comparison (n : ℕ) (hn : 0 < n) :
    toComponents L n hn ≫ (componentsIso K L n).hom =
      (branchesIso K L n).hom ≫ (F).map (toComponents K n hn) := by
  apply Sigma.hom_ext
  intro ib
  rcases ib with ⟨i, b⟩
  cases b <;>
    simp [toComponents, endpoint, componentsIso, branchesIso, componentι,
      ← Functor.map_comp, Category.assoc, zero_component_assoc, infinity_component_assoc]

@[reassoc] theorem toNodes_comparison (n : ℕ) :
    toNodes L n ≫ (nodesIso K L n).hom =
      (branchesIso K L n).hom ≫ (F).map (toNodes K n) := by
  apply Sigma.hom_ext
  rintro ⟨i, b⟩
  simp [toNodes, nodeι, nodesIso, branchesIso, ← Functor.map_comp]

variable (n : ℕ) [NeZero n] (hn : 0 < n) {C : Over (Spec (.of K))}
  (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
include h in
/-- The actual base-changed cocone is the specified polygon diagram over the new field. -/
theorem isPushout : IsPushout (toComponents L n hn) (toNodes L n)
    ((componentsIso K L n).hom ≫ (F).map p)
    ((nodesIso K L n).hom ≫ (F).map q) := by
  apply (PolygonPinchingAffineBaseChange.pinching_pullback K L n hn p q h).of_iso'
    (branchesIso K L n) (componentsIso K L n) (nodesIso K L n) (Iso.refl _)
  · exact (toComponents_comparison K L n hn).symm
  · exact (toNodes_comparison K L n).symm
  · simp [PinchingChartBaseChange.parameter, ProjectiveLineProductCharts.parameterToBase]
  · simp [PinchingChartBaseChange.parameter, ProjectiveLineProductCharts.parameterToBase]

omit [Algebra K L] in
include h in
/-- Every affine field-valued base map produces an actual polygon cocone. -/
theorem exists_cocone (g : Spec (.of L) ⟶ Spec (.of K)) :
    ∃ (p' : components L n ⟶ (Over.pullback g).obj C)
      (q' : nodes L n ⟶ (Over.pullback g).obj C),
      IsPushout (toComponents L n hn) (toNodes L n) p' q' := by
  let := (Spec.preimage g).hom.toAlgebra
  have hh : ∃ (p' : components L n ⟶ (F).obj C)
      (q' : nodes L n ⟶ (F).obj C),
      IsPushout (toComponents L n hn) (toNodes L n) p' q' :=
    ⟨_, _, isPushout K L n hn p q h⟩
  have he : ProjectiveLineProductCharts.parameterToBase K L = g := Spec.map_preimage g
  rw [he] at hh
  exact hh

omit [Algebra K L] in
include h in
/-- The specified diagram also presents any chosen geometric pullback square. -/
theorem exists_cocone_of_isPullback (g : Spec (.of L) ⟶ Spec (.of K))
    {Y : Scheme} (fst : Y ⟶ C.left) (snd : Y ⟶ Spec (.of L))
    (hs : IsPullback fst snd C.hom g) :
    ∃ (p' : components L n ⟶ Over.mk snd) (q' : nodes L n ⟶ Over.mk snd),
      IsPushout (toComponents L n hn) (toNodes L n) p' q' := by
  obtain ⟨p', q', hh⟩ := exists_cocone K L n hn p q h g
  let e : Over.mk snd ≅ (Over.pullback g).obj C :=
    Over.isoMk hs.isoPullback (by simp)
  exact ⟨p' ≫ e.inv, q' ≫ e.inv,
    hh.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.symm
      (by simp) (by simp) (by simp) (by simp)⟩
end FLT.Mazur.PolygonFieldExtension
