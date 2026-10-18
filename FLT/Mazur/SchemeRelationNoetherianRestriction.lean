/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationDoubleRestriction
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Noetherianity of the full independent two-endpoint restriction

An original relation of finite type and a finite-type new source give a
Noetherian full relation whenever that source is Noetherian. Both independent
endpoints and the entire original arrow are retained; affineness is unnecessary.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeRelationRestriction
set_option backward.isDefEq.respectTransparency false
variable {A X Y : Scheme} (p q : A ⟶ X) (k : Y ⟶ X)
  [LocallyOfFiniteType p] [LocallyOfFiniteType k]

/-- The full first endpoint is locally of finite type by its two actual pullbacks. -/
theorem fst_locallyOfFiniteType : LocallyOfFiniteType (fst p q k) := by
  unfold fst doubleDomain
  infer_instance

/-- The full relation is locally Noetherian over a locally Noetherian new source. -/
theorem doubleDomain_locallyNoetherian [IsLocallyNoetherian Y] :
    IsLocallyNoetherian (doubleDomain p q k) := by
  let _ := fst_locallyOfFiniteType p q k
  exact LocallyOfFiniteType.isLocallyNoetherian (fst p q k)

variable [QuasiCompact p] [QuasiCompact k]

omit [LocallyOfFiniteType p] [LocallyOfFiniteType k] in
/-- Quasi-compactness keeps all independently lifted arrows in a compact source. -/
theorem fst_quasiCompact : QuasiCompact (fst p q k) := by
  unfold fst doubleDomain
  infer_instance

/-- The full double restriction is Noetherian, with no affine-relation hypothesis. -/
theorem doubleDomain_isNoetherian [IsNoetherian Y] :
    IsNoetherian (doubleDomain p q k) := by
  let _ := doubleDomain_locallyNoetherian p q k
  let _ := fst_quasiCompact p q k
  let _ := QuasiCompact.compactSpace_of_compactSpace (fst p q k)
  exact ⟨⟩

end FLT.Mazur.SchemeRelationRestriction
