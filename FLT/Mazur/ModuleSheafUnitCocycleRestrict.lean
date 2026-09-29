/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafUnitCocycle
public import FLT.Mazur.DivisorInvertibleSheaf

/-!
# Trivializations of a module descended from units

Evaluation on a chart is inverted by multiplication by the transition units.
These maps commute with restriction and give local rank one on a covering family.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve.ModuleSheafUnitCocycle.Cocycle

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (g : Cocycle U)

/-- Evaluation on the chosen component, transported across `V ∩ U i = V`. -/
def evaluate (i : ι) {V : X.Opens} (hi : V ≤ U i) (s : g.sections V) : Γ(X, V) :=
  res (le_inf le_rfl hi) (s.1 i)

/-- Extend a function on one chart by its transition functions. -/
def extend (i : ι) {V : X.Opens} (hi : V ≤ U i) (r : Γ(X, V)) : g.sections V :=
  ⟨fun j ↦ (g.unit j i (V ⊓ U j) inf_le_right (inf_le_left.trans hi) :
    Γ(X, V ⊓ U j)) * res inf_le_left r, by
    intro j k W hj hk
    simp only [map_mul, g.natural, res_res]
    rw [← mul_assoc]
    congr 1
    exact congrArg Units.val (g.cocycle j k i W (hj.trans inf_le_right)
      (hk.trans inf_le_right) ((hk.trans inf_le_left).trans hi)) |>.symm⟩

@[simp] lemma evaluate_extend (i : ι) {V : X.Opens} (hi : V ≤ U i) (r : Γ(X, V)) :
    g.evaluate i hi (g.extend i hi r) = r := by
  simp [evaluate, extend, g.refl]

@[simp] lemma extend_evaluate (i : ι) {V : X.Opens} (hi : V ≤ U i)
    (s : g.sections V) : g.extend i hi (g.evaluate i hi s) = s := by
  apply Subtype.ext
  funext j
  change _ * res inf_le_left (res (le_inf le_rfl hi) (s.1 i)) = s.1 j
  rw [res_res]
  exact (s.2 j i (V ⊓ U j) le_rfl
    (le_inf inf_le_left (inf_le_left.trans hi))).symm.trans (res_self _ _)

/-- Evaluation is an additive equivalence on every subopen of the chart. -/
def evaluationEquiv (i : ι) {V : X.Opens} (hi : V ≤ U i) :
    g.sections V ≃+ Γ(X, V) where
  toFun := g.evaluate i hi
  invFun := g.extend i hi
  left_inv := g.extend_evaluate i hi
  right_inv := g.evaluate_extend i hi
  map_add' _ _ := map_add _ _ _

lemma evaluate_smul (i : ι) {V : X.Opens} (hi : V ≤ U i) (r : Γ(X, V))
    (s : g.sections V) : g.evaluate i hi (r • s) = r * g.evaluate i hi s := by
  change res _ (res inf_le_left r * s.1 i) = _
  simp only [map_mul, res_res, res_self]
  rfl

/-- Evaluation commutes with restriction to smaller opens. -/
lemma evaluate_restrict (i : ι) {V W : X.Opens} (hi : V ≤ U i) (h : W ≤ V)
    (s : g.sections V) :
    g.evaluate i (h.trans hi) (g.restrict h s) = res h (g.evaluate i hi s) := by
  simp only [evaluate, restrict_apply, res_res]

/-- The inverse trivialization also commutes with restriction. -/
lemma extend_restrict (i : ι) {V W : X.Opens} (hi : V ≤ U i) (h : W ≤ V)
    (r : Γ(X, V)) :
    g.restrict h (g.extend i hi r) = g.extend i (h.trans hi) (res h r) := by
  apply (g.evaluationEquiv i (h.trans hi)).injective
  change g.evaluate i (h.trans hi) _ = g.evaluate i (h.trans hi) _
  rw [g.evaluate_restrict i hi h, g.evaluate_extend, g.evaluate_extend]

/-- Change of component is multiplication by the specified transition unit. -/
lemma transition (i j : ι) {V : X.Opens} (hi : V ≤ U i) (hj : V ≤ U j)
    (s : g.sections V) :
    g.evaluate i hi s = (g.unit i j V hi hj : Γ(X, V)) * g.evaluate j hj s :=
  s.2 i j V (le_inf le_rfl hi) (le_inf le_rfl hj)

/-- Evaluation trivializes the sheaf on any open contained in the chosen chart. -/
def onOpenIso (i : ι) (V : X.Opens) (hi : V ≤ U i) :
    g.sheaf.restrict V.ι ≅ structureModule V.toScheme := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun W ↦ ?_) ?_)
  · refine ModuleCat.isoMk
      (AddEquiv.toAddCommGrpIso
        (g.evaluationEquiv i ((V.ι_image_le W.unop).trans hi))) ?_
    intro (r : Γ(V.toScheme, W.unop))
    ext (s : g.sections (V.ι ''ᵁ W.unop))
    let r' : Γ(X, V.ι ''ᵁ W.unop) := r
    change r' * g.evaluate i ((V.ι_image_le W.unop).trans hi) s =
      g.evaluate i ((V.ι_image_le W.unop).trans hi)
        ((((g.sheaf.restrict V.ι).smul r).hom) s)
    change r' * g.evaluate i ((V.ι_image_le W.unop).trans hi) s =
      g.evaluate i ((V.ι_image_le W.unop).trans hi) ((V.ι.appIso W.unop).inv r • s)
    rw [Scheme.Opens.ι_appIso]
    exact (g.evaluate_smul i ((V.ι_image_le W.unop).trans hi) r' s).symm
  · intro W Z f
    ext s
    exact g.evaluate_restrict i ((V.ι_image_le W.unop).trans hi)
      (V.ι.image_mono (leOfHom f.unop)) s

/-- Component evaluation is an isomorphism on the open subscheme of each chart. -/
def restrictIso (i : ι) :
    g.sheaf.restrict (U i).ι ≅ structureModule (U i).toScheme :=
  g.onOpenIso i (U i) le_rfl

/-- The sheaf trivializations obey the transition equation on every common subopen. -/
lemma onOpenIso_transition (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j)
    (W : V.toScheme.Opens) (s : g.sections (V.ι ''ᵁ W)) :
    (g.onOpenIso i V hi).hom.app W s =
      (g.unit i j (V.ι ''ᵁ W) ((V.ι_image_le W).trans hi)
        ((V.ι_image_le W).trans hj) : Γ(X, V.ι ''ᵁ W)) *
          (show Γ(X, V.ι ''ᵁ W) from (g.onOpenIso j V hj).hom.app W s) :=
  g.transition i j _ _ s

/-- Changing from the j-th trivialization to the i-th multiplies by `g_ij`. -/
lemma onOpenIso_change (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j)
    (W : V.toScheme.Opens) (r : Γ(V.toScheme, W)) :
    ((g.onOpenIso j V hj).inv ≫ (g.onOpenIso i V hi).hom).app W r =
      (g.unit i j (V.ι ''ᵁ W) ((V.ι_image_le W).trans hi)
        ((V.ι_image_le W).trans hj) : Γ(X, V.ι ''ᵁ W)) *
          (show Γ(X, V.ι ''ᵁ W) from r) := by
  change g.evaluate i ((V.ι_image_le W).trans hi)
    (g.extend j ((V.ι_image_le W).trans hj) r) = _
  rw [g.transition i j ((V.ι_image_le W).trans hi) ((V.ι_image_le W).trans hj), g.evaluate_extend]

/-- The forward sheaf morphism evaluates the chosen component on every open. -/
@[simp] lemma restrictIso_hom_app (i : ι) (W : (U i).toScheme.Opens)
    (s : g.sections ((U i).ι ''ᵁ W)) :
    (g.restrictIso i).hom.app W s = g.evaluate i ((U i).ι_image_le W) s := rfl

/-- The inverse sheaf morphism multiplies by the transition units on every open. -/
@[simp] lemma restrictIso_inv_app (i : ι) (W : (U i).toScheme.Opens)
    (r : Γ((U i).toScheme, W)) :
    (g.restrictIso i).inv.app W r = g.extend i ((U i).ι_image_le W) r := rfl

/-- A covering family of charts proves local freeness of rank one. -/
theorem locallyFreeRankOne (hU : iSup U = ⊤) : LocallyFreeRankOne g.sheaf := by
  intro x
  have hx : x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact ⟨U i, hi, ⟨g.restrictIso i⟩⟩

end FLT.Mazur.FCurve.ModuleSheafUnitCocycle.Cocycle
