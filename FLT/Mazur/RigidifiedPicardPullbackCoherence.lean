/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RigidifiedPicardPullback
public import FLT.Mazur.SchemePullbackSquareComposition
public import FLT.Mazur.DivisorLinePullbackIdentity

/-!
# Coherence of the prescribed rigidified pullbacks

The actual pullback unit and composition isomorphisms preserve the transported
trivializations. These statements concern the original representatives.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
open FCurve FCurve.LineSheafSectionRigidity SchemePullbackSquare
variable {X Y Z S T U : Scheme.{u}}

/-- The prescribed pullback unitor preserves the original rigidification. -/
theorem rigidifiedBundlePullback_id_preserves (s : S ⟶ X) (L : RigidifiedBundle s) :
    (Scheme.Modules.pullback s).map ((Scheme.Modules.pullbackId X).hom.app L.1.val) ≫
        L.2.hom =
      (rigidifiedBundlePullback s s (𝟙 X) (𝟙 S) (by simp) L).2.hom := by
  change _ = (squareIso s s (𝟙 X) (𝟙 S) _).hom.app L.1.val ≫
    (Scheme.Modules.pullback (𝟙 S)).map L.2.hom ≫ (modulePullbackUnitIso (𝟙 S)).hom
  rw [modulePullbackUnitIso_id]
  exact (reconstruction_identity s (𝟙 X) (𝟙 S) rfl rfl (by simp) L.2).symm

/-- Identity pullback carries its canonical rigidification-preserving comparison. -/
def rigidifiedBundlePullbackId (s : S ⟶ X) (L : RigidifiedBundle s) :
    RigidifiedIso s (rigidifiedBundlePullback s s (𝟙 X) (𝟙 S) (by simp) L).2 L.2 :=
  ⟨(Scheme.Modules.pullbackId X).app L.1.val,
    rigidifiedBundlePullback_id_preserves s L⟩

variable (s : S ⟶ X) (t : T ⟶ Y) (r : U ⟶ Z)
  (p : Y ⟶ X) (b : T ⟶ S) (q : Z ⟶ Y) (c : U ⟶ T)
  (w : t ≫ p = b ≫ s) (v : r ≫ q = c ≫ t)

/-- The prescribed composition comparison preserves the transported trivializations. -/
theorem rigidifiedBundlePullback_comp_preserves (L : RigidifiedBundle s) :
    (Scheme.Modules.pullback r).map
        ((Scheme.Modules.pullbackComp q p).hom.app L.1.val) ≫
      (rigidifiedBundlePullback s r (q ≫ p) (c ≫ b)
        (composite_square s t r p b q c w v) L).2.hom =
    (rigidifiedBundlePullback t r q c v
      (rigidifiedBundlePullback s t p b w L)).2.hom := by
  change (Scheme.Modules.pullback r).map
      ((Scheme.Modules.pullbackComp q p).hom.app L.1.val) ≫
      ((squareIso s r (q ≫ p) (c ≫ b) _).hom.app L.1.val ≫
        (Scheme.Modules.pullback (c ≫ b)).map L.2.hom ≫
        (modulePullbackUnitIso (c ≫ b)).hom) =
    (squareIso t r q c v).hom.app ((Scheme.Modules.pullback p).obj L.1.val) ≫
      (Scheme.Modules.pullback c).map
        ((squareIso s t p b w).hom.app L.1.val ≫
          (Scheme.Modules.pullback b).map L.2.hom ≫ (modulePullbackUnitIso b).hom) ≫
      (modulePullbackUnitIso c).hom
  simp only [Functor.map_comp, Category.assoc]
  rw [modulePullbackUnitIso_comp_hom]
  simpa only [Functor.map_comp, Category.assoc] using congrArg
    (fun k ↦ k ≫ (modulePullbackUnitIso (c ≫ b)).hom)
    (reconstruction_composition s t r p b q c w v L.2).symm

/-- Composition pullback carries its actual canonical preserving isomorphism. -/
def rigidifiedBundlePullbackComp (L : RigidifiedBundle s) :
    RigidifiedIso r
      (rigidifiedBundlePullback t r q c v (rigidifiedBundlePullback s t p b w L)).2
      (rigidifiedBundlePullback s r (q ≫ p) (c ≫ b)
        (composite_square s t r p b q c w v) L).2 :=
  ⟨(Scheme.Modules.pullbackComp q p).app L.1.val,
    rigidifiedBundlePullback_comp_preserves s t r p b q c w v L⟩

end FLT.Mazur.SchemePicard
