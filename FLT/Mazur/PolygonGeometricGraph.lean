/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonActionGraph
public import FLT.Mazur.PolygonFieldExtension

/-!
# Incidence and intrinsic translations on geometric fibers

Each chosen field-valued pullback square carries the specified polygon
cocone, whose actual components and nodes form the cyclic incidence graph.
This theorem concerns its intrinsic action; comparison with the pulled-back
action is a separate naturality statement.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.PolygonGeometricGraph
open PolygonPinching PolygonActionGraph PolygonActionTranslation
variable (K L : Type u) [Field K] [Field L]
  (n : ℕ) [NeZero n] (hn : 0 < n) {C : Over (Spec (.of K))}
  (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
include h in
/-- Actual cyclic graph and intrinsic translations on every chosen field-valued fiber. -/
theorem fiber_graph (g : Spec (.of L) ⟶ Spec (.of K))
    {Y : Scheme} (fst : Y ⟶ C.left) (snd : Y ⟶ Spec (.of L))
    (hs : IsPullback fst snd C.hom g) :
    ∃ (p' : components L n ⟶ Over.mk snd) (q' : nodes L n ⟶ Over.mk snd)
      (hh : IsPushout (toComponents L n hn) (toNodes L n) p' q'),
    let := polygon_lfp L n hn p' q' hh
    (∀ i j, (edges L n hn p' q' hh j).val ∈ (vertices L n hn p' q' hh i).val ↔
      i = j ∨ i = next hn j) ∧
    (∀ (a : Lˣ) (b : ZMod n) i,
      (translation L n hn p' q' hh a b).left '' (vertices L n hn p' q' hh i).val =
        (vertices L n hn p' q' hh (rotateIndex b i)).val) ∧
    (∀ (a : Lˣ) (b : ZMod n) j,
      (translation L n hn p' q' hh a b).left (edges L n hn p' q' hh j).val =
        (edges L n hn p' q' hh (rotateIndex b j)).val) := by
  obtain ⟨p', q', hh⟩ :=
    PolygonFieldExtension.exists_cocone_of_isPullback K L n hn p q h g fst snd hs
  refine ⟨p', q', hh, ?_⟩
  let := polygon_lfp L n hn p' q' hh
  exact ⟨incidence L n hn p' q' hh, vertex_translation L n hn p' q' hh,
    edge_translation L n hn p' q' hh⟩
end FLT.Mazur.PolygonGeometricGraph
