/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertClosedEnvelopeInterior
public import Mathlib.Topology.Connected.Clopen

/-!
# Initial full fibers from connected independent translation fibers

Reflexivity supplies one point in the original relation above each source
point. Closedness of the original endpoint makes its envelope image clopen;
connectedness then fills the entire independent fiber, including nonsplit
residue branches. Neither fullness nor a relation representative for each
branch is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "j" => Over.Hom.left (toEnvelope f hL d V c k)
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "e" => equivalence f hL d V c k

omit [Etale V.hom] [IsAffine V.left] [IsOpenImmersion k.left] in
/-- Reflexivity constructs an actual original relation point above each source point. -/
theorem envelopeFiber_identity (x : A.left) :
    π (j ((e).r.left x)) = x := by
  have h : (e).r ≫ toEnvelope f hL d V c k ≫ (prod.fst : prod A V ⟶ A) = 𝟙 A := by
    rw [toEnvelope_test, (e).reflexivity₂]
  exact congrArg (fun t : A ⟶ A ↦ t.left x) h

variable [UniversallyClosed (snd f hL d V c k).left]

omit [Etale V.hom] in
/-- A connected independent fiber is filled by the original relation, starting from identity. -/
theorem fullEnvelopeLocus_of_connected_fiber (x : A.left)
    (hc : _root_.IsPreconnected (π ⁻¹' {x})) : x ∈ fullEnvelopeLocus f hL d V c k := by
  apply (mem_fullFiberLocus π (j).opensRange x).mpr
  have hj : IsClopen ((j).opensRange : Set (prod A V).left) :=
    ⟨(toEnvelope_isClosedMap f hL d V c k).isClosed_range, (j).opensRange.isOpen⟩
  have hn : ((π ⁻¹' {x}) ∩ ((j).opensRange : Set (prod A V).left)).Nonempty :=
    ⟨j ((e).r.left x), envelopeFiber_identity f hL d V c k x, (e).r.left x, rfl⟩
  intro z hz
  exact hc.subset_isClopen hj hn hz

omit [Etale V.hom] in
/-- A connected entire envelope and a source point force the original envelope to be full. -/
theorem toEnvelope_surjective_of_connected
    [PreconnectedSpace (prod A V).left] [Nonempty A.left] : Function.Surjective j := by
  have hj : IsClopen ((j).opensRange : Set (prod A V).left) :=
    ⟨(toEnvelope_isClosedMap f hL d V c k).isClosed_range, (j).opensRange.isOpen⟩
  obtain ⟨x⟩ := ‹Nonempty A.left›
  have hn : ((j).opensRange : Set (prod A V).left).Nonempty :=
    ⟨j ((e).r.left x), (e).r.left x, rfl⟩
  intro z
  exact Set.eq_univ_iff_forall.mp (hj.eq_univ hn) z

omit [Etale V.hom] in
/-- Fiberwise connectedness constructs full-fiber coverage on the whole original source. -/
theorem fullEnvelopeLocus_eq_univ_of_connected_fibers
    (hc : ∀ x : A.left, _root_.IsPreconnected (π ⁻¹' {x})) :
    fullEnvelopeLocus f hL d V c k = Set.univ :=
  Set.eq_univ_of_forall (fun x ↦ fullEnvelopeLocus_of_connected_fiber f hL d V c k x (hc x))

end FLT.Mazur.HilbertChart.AffineRestriction
