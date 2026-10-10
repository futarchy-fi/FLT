/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOpenImmersionSections

/-!
# Projection sections with specified preimage coordinates

An ambient projection can be evaluated using a specified equality of opens.
These coordinates retain restriction naturality and the chosen chart recovery.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafProjectionSections

variable {X Y : Scheme.{u}} (i : Y ⟶ X) (G : X.Modules) (M : Y.Modules)
  (q : G ⟶ (pushforward i).obj M)

/-- Evaluate a projection with the specified preimage identification. -/
def sections (W : X.Opens) (U : Y.Opens) (h : i ⁻¹ᵁ W = U) :
    Γ(G, W) ⟶ Γ(M, U) :=
  q.app W ≫ M.presheaf.map (eqToHom h.symm).op

/-- Specified preimage coordinates commute with the original restriction maps. -/
lemma sections_naturality {W Z : X.Opens} (k : W ⟶ Z) {U V : Y.Opens}
    (hW : i ⁻¹ᵁ W = U) (hZ : i ⁻¹ᵁ Z = V) (l : U ⟶ V) :
    G.presheaf.map k.op ≫ sections i G M q W U hW =
      sections i G M q Z V hZ ≫ M.presheaf.map l.op := by
  subst U
  subst V
  ext s
  change M.presheaf.map (𝟙 _) (q.app W (G.presheaf.map k.op s)) =
    M.presheaf.map l.op (M.presheaf.map (𝟙 _) (q.app Z s))
  rw [M.presheaf.map_id, M.presheaf.map_id]
  exact congrArg (fun t ↦ t s) (q.mapPresheaf.naturality k.op)

/-- Chart recovery is exactly projection evaluation with its image/preimage transport. -/
lemma recovery_sections [IsOpenImmersion i]
    (e : G.restrict i ⟶ M)
    (he : e = (restrictFunctor i).map q ≫ (restrictFunctorAdjCounitIso i).hom.app M)
    (U : Y.Opens) (W : X.Opens) (h : i ''ᵁ U = W) :
    G.presheaf.map (eqToHom h).op ≫ (G.restrictAppIso i U).inv ≫ e.app U =
      sections i G M q W U ((congrArg (fun T ↦ i ⁻¹ᵁ T) h).symm.trans
        (i.preimage_image_eq U)) := by
  subst W
  rw [he]
  simp only [eqToHom_refl, op_id]
  rw [G.presheaf.map_id, Category.id_comp]
  rfl

end FLT.Mazur.ModuleSheafProjectionSections
