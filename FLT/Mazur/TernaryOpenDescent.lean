/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BinaryOpenDescent

/-!
# Descent along three open charts

Pairwise agreement on the three pullbacks suffices for gluing, with no
separatedness assumption on the target.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.TernaryOpenDescent

variable {U V W X Y : Scheme.{u}} (i : U ⟶ X) (j : V ⟶ X) (k : W ⟶ X)
  [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion k]
  (hc : ∀ x : X, x ∈ Set.range i ∨ x ∈ Set.range j ∨ x ∈ Set.range k)

/-- The open cover given by three jointly covering open immersions. -/
def cover : X.OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (Option Bool)
    (fun t ↦ match t with | none => U | some false => V | some true => W)
    (fun t ↦ match t with | none => i | some false => j | some true => k)
    (fun x ↦ by
      rcases hc x with h | h | h
      · exact ⟨none, h⟩
      · exact ⟨some false, h⟩
      · exact ⟨some true, h⟩)
    (fun t ↦ by rcases t with _ | (_ | _) <;> infer_instance)

/-- Agreement on an intersection is symmetric. -/
theorem flip_compatible (f : U ⟶ Y) (g : V ⟶ Y)
    (h : pullback.fst i j ≫ f = pullback.snd i j ≫ g) :
    pullback.fst j i ≫ g = pullback.snd j i ≫ f := by
  apply (cancel_epi (pullbackSymmetry i j).hom).mp
  simpa using h.symm

omit [IsOpenImmersion i] in
/-- Disjoint charts have automatic overlap compatibility. -/
theorem disjoint_compatible (f : U ⟶ Y) (g : V ⟶ Y)
    (h : Disjoint (Set.range i) (Set.range j)) :
    pullback.fst i j ≫ f = pullback.snd i j ≫ g := by
  apply Scheme.hom_ext_of_forall
  intro x
  have he : i (pullback.fst i j x) = j (pullback.snd i j x) :=
    congrArg (fun a ↦ a x) (pullback.condition (f := i) (g := j))
  exact False.elim (Set.disjoint_left.mp h ⟨_, rfl⟩ ⟨_, he.symm⟩)

variable (f : U ⟶ Y) (g : V ⟶ Y) (h : W ⟶ Y)
  (hfg : pullback.fst i j ≫ f = pullback.snd i j ≫ g)
  (hfh : pullback.fst i k ≫ f = pullback.snd i k ≫ h)
  (hgh : pullback.fst j k ≫ g = pullback.snd j k ≫ h)

/-- The three local maps, as a dependent family on the cover. -/
def maps (t : Option Bool) : (cover i j k hc).X t ⟶ Y :=
  match t with | none => f | some false => g | some true => h

include hfg hfh hgh in
/-- Pairwise compatibility for every ordered pair of charts. -/
theorem compatible : ∀ a b, pullback.fst ((cover i j k hc).f a)
    ((cover i j k hc).f b) ≫ maps i j k hc f g h a =
    pullback.snd _ _ ≫ maps i j k hc f g h b := by
  rintro (_ | (_ | _)) (_ | (_ | _))
  · exact congrArg (fun t ↦ t ≫ f) ((cancel_mono i).mp (pullback.condition (f := i) (g := i)))
  · exact hfg
  · exact hfh
  · exact flip_compatible i j f g hfg
  · exact congrArg (fun t ↦ t ≫ g) ((cancel_mono j).mp (pullback.condition (f := j) (g := j)))
  · exact hgh
  · exact flip_compatible i k f h hfh
  · exact flip_compatible j k g h hgh
  · exact congrArg (fun t ↦ t ≫ h) ((cancel_mono k).mp (pullback.condition (f := k) (g := k)))

/-- Glue the three maps. -/
def desc : X ⟶ Y :=
  (cover i j k hc).glueMorphisms (maps i j k hc f g h)
    (compatible i j k hc f g h hfg hfh hgh)

@[reassoc (attr := simp)]
theorem first_desc : i ≫ desc i j k hc f g h hfg hfh hgh = f :=
  (cover i j k hc).ι_glueMorphisms _ _ none

@[reassoc (attr := simp)]
theorem second_desc : j ≫ desc i j k hc f g h hfg hfh hgh = g :=
  (cover i j k hc).ι_glueMorphisms _ _ (some false)

@[reassoc (attr := simp)]
theorem third_desc : k ≫ desc i j k hc f g h hfg hfh hgh = h :=
  (cover i j k hc).ι_glueMorphisms _ _ (some true)

end FLT.Mazur.TernaryOpenDescent
