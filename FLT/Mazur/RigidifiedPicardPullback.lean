/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RigidifiedPicardClasses
public import FLT.Mazur.SchemePullbackSquare

/-!
# Pulling back actual rigidified line bundles

The trivialization uses the prescribed comparison around the commuting square,
followed by pullback of the original trivialization and the structural unit map.
Actual rigidification-preserving isomorphisms pull back to such isomorphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
open FCurve FCurve.LineSheafSectionRigidity
variable {X Y S T : Scheme.{u}} (s : S ⟶ X) (t : T ⟶ Y)
  (p : Y ⟶ X) (b : T ⟶ S) (w : t ≫ p = b ≫ s)

/-- Pullback retains the actual bundle and transports its chosen trivialization. -/
def rigidifiedBundlePullback (L : RigidifiedBundle s) : RigidifiedBundle t :=
  ⟨⟨(Scheme.Modules.pullback p).obj L.1.val, L.1.property.pullback p⟩,
    (SchemePullbackSquare.squareIso s t p b w).app L.1.val ≪≫
      (Scheme.Modules.pullback b).mapIso L.2 ≪≫ modulePullbackUnitIso b⟩

/-- The pulled rigidified bundle has precisely the original Picard pullback class. -/
theorem rigidifiedBundlePullback_kernel (L : RigidifiedBundle s) :
    (rigidifiedBundleKernel t (rigidifiedBundlePullback s t p b w L)).val =
      pullback p (rigidifiedBundleKernel s L).val := rfl

/-- The original pulled isomorphism preserves the transported trivializations. -/
def rigidifiedIsoPullback {L M : RigidifiedBundle s} (i : RigidifiedIso s L.2 M.2) :
    RigidifiedIso t (rigidifiedBundlePullback s t p b w L).2
      (rigidifiedBundlePullback s t p b w M).2 := by
  refine ⟨(Scheme.Modules.pullback p).mapIso i.val, ?_⟩
  have hn := (SchemePullbackSquare.squareIso s t p b w).hom.naturality i.val.hom
  change (Scheme.Modules.pullback t).map ((Scheme.Modules.pullback p).map i.val.hom) ≫
      (SchemePullbackSquare.squareIso s t p b w).hom.app M.1.val =
    (SchemePullbackSquare.squareIso s t p b w).hom.app L.1.val ≫
      (Scheme.Modules.pullback b).map ((Scheme.Modules.pullback s).map i.val.hom) at hn
  change (Scheme.Modules.pullback t).map ((Scheme.Modules.pullback p).map i.val.hom) ≫
      ((SchemePullbackSquare.squareIso s t p b w).hom.app M.1.val ≫
        (Scheme.Modules.pullback b).map M.2.hom ≫ (modulePullbackUnitIso b).hom) =
    (SchemePullbackSquare.squareIso s t p b w).hom.app L.1.val ≫
      (Scheme.Modules.pullback b).map L.2.hom ≫ (modulePullbackUnitIso b).hom
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, i.property]

/-- Actual pullback descends to rigidified isomorphism classes. -/
def rigidifiedPicPullback : RigidifiedPic s → RigidifiedPic t :=
  Quotient.map (rigidifiedBundlePullback s t p b w) (by
    intro L M h
    obtain ⟨i⟩ := h
    exact ⟨rigidifiedIsoPullback s t p b w i⟩)

/-- Forgetting a pulled rigidification is the original Picard pullback on every class. -/
theorem rigidifiedPicPullback_kernel (a : RigidifiedPic s) :
    (rigidifiedKernel t (rigidifiedPicPullback s t p b w a)).val =
      pullback p (rigidifiedKernel s a).val :=
  Quotient.inductionOn a (fun _ ↦ rfl)

end FLT.Mazur.SchemePicard
