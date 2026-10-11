/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalPointConditionLine
public import FLT.Mazur.RationalPointConditionRank

/-!
# A rank-dropping condition that already spreads over a smooth parameter space

The chosen rational point determines a lift to the universal parameter curve.
The actual relative line there has acyclic geometric restriction and exactly
one fewer section. No extension of a field line is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor universalPointConditionLine

variable {k : Type} [Field k] [IsAlgClosed k]
  {X Y S : Scheme} [IsReduced Y] (f : X ⟶ S)
  [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  {p : Y ⟶ X} {q : Y ⟶ Spec (.of k)} {g : Spec (.of k) ⟶ S}
  [IsProper q] [SmoothOfRelativeDimension 1 q] (H : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)

include hL in
/-- The next point condition lifts to an actual line on the smooth universal family. -/
theorem exists_universal_point_rank_drop
    [Subsingleton (ModuleScalarH q ((Scheme.Modules.pullback p).obj L) 1)]
    (hp : 0 < Module.finrank k (ModuleScalarH q ((Scheme.Modules.pullback p).obj L) 0)) :
    ∃ (s : Spec (.of k) ⟶ Y) (hs : s ≫ q = 𝟙 _),
      Subsingleton (ModuleScalarH q
        ((Scheme.Modules.pullback (pointConditionMap f H s hs)).obj
          (universalPointConditionLine f L)) 1) ∧
      Module.finrank k (ModuleScalarH q
        ((Scheme.Modules.pullback (pointConditionMap f H s hs)).obj
          (universalPointConditionLine f L)) 0) + 1 =
        Module.finrank k (ModuleScalarH q ((Scheme.Modules.pullback p).obj L) 0) := by
  obtain ⟨s, hs, hz, hr⟩ := exists_rational_point_rank_drop q (hL.pullback p) hp
  let e := universalPointConditionLineIso f L H s hs
  let _ : Subsingleton (ModuleH
      (ModuleSheafTensor.tensor (idealModule s.ker) ((Scheme.Modules.pullback p).obj L)) 1) := hz
  refine ⟨s, hs, moduleH_subsingleton_of_iso e 1, ?_⟩
  exact (congrArg (· + 1)
    ((moduleScalarHFunctor q 0).mapIso e).toLinearEquiv.finrank_eq).trans hr

end FLT.Mazur.FCurve
