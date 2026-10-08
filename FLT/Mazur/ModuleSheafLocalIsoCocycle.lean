/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafLocalIsoTransport

/-!
# Cocycle under equality transport of an open

Changing the name of the common open preserves a sectionwise cocycle.
The transport is proved with abstract modules before applying it to the
effectively descended chart sheaves.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.ModuleSheafMorphismGluing

/-- Equality transport of all three transition isomorphisms preserves their cocycle. -/
theorem localIso_cast_cocycle {X : Scheme.{u}} {M N P : X.Modules}
    {U V : X.Opens} (h : U = V)
    (a : M.over U ≅ N.over U) (b : N.over U ≅ P.over U) (c : M.over U ≅ P.over U)
    (W : X.Opens) (hW : W ≤ V) (s : Γ(M, W))
    (hc : localApp b.hom (hW.trans_eq h.symm)
        (localApp a.hom (hW.trans_eq h.symm) s) =
      localApp c.hom (hW.trans_eq h.symm) s) :
    localApp (cast (congrArg (fun A ↦ N.over A ≅ P.over A) h) b).hom hW
        (localApp (cast (congrArg (fun A ↦ M.over A ≅ N.over A) h) a).hom hW s) =
      localApp (cast (congrArg (fun A ↦ M.over A ≅ P.over A) h) c).hom hW s := by
  subst V
  exact hc

end FLT.Mazur.ModuleSheafMorphismGluing
