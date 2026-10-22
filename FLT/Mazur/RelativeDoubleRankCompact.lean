/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDoubleRankThickenings

/-!
# Compact full independent rank stages

Noetherianity of the original topological base makes every rank-stage map
quasi-compact. Consequently compact coefficient tests have compact full
two-rank stages, even when the coefficient ring is not Noetherian.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  [NoetherianSpace S] (x y : B ⟶ S) (n m r s : ℕ)

instance rankThickeningMap_quasiCompact : QuasiCompact (rankThickeningMap E n r) := by
  let _ : NoetherianSpace (rankImageOpen E n).toScheme :=
    NoetherianSpace.set (rankImageOpen E n : Set S)
  let _ : QuasiCompact (rankImageOpen E n).ι := inferInstance
  unfold rankThickeningMap
  infer_instance

instance rankPullbackMap_quasiCompact : QuasiCompact (rankPullbackMap E x n r) := by
  unfold rankPullbackMap
  infer_instance

instance doubleRankMap_quasiCompact : QuasiCompact (doubleRankMap E x y n m r s) := by
  unfold doubleRankMap
  infer_instance

instance rankPullbackThickening_compact [CompactSpace B] :
    CompactSpace (rankPullbackThickening E x n r) :=
  QuasiCompact.compactSpace_of_compactSpace (rankPullbackMap E x n r)

instance doubleRankThickening_compact [CompactSpace B] :
    CompactSpace (doubleRankThickening E x y n m r s) :=
  QuasiCompact.compactSpace_of_compactSpace (doubleRankMap E x y n m r s)

end FLT.Mazur.RelativeOrderedTuples
