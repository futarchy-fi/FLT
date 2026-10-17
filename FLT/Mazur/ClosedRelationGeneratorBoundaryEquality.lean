/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedRelationGeneratorSections

/-!
# Original boundary equality from tests on an etale generator

The ambient invariant function and the boundary invariant function agree
exactly when they agree on scheme-valued boundary tests of the generator.
The proof uses invariant descent, with no saturation of the generator assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.RelativeRelationOrbit
open InvariantOpenRelationDiagram
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} {A U C B : Over S} {p q : A ⟶ U} {r s : C ⟶ B}
  (e : CategoryTheory.EquivalenceRelation p q)
  (ec : CategoryTheory.EquivalenceRelation r s) (i : B ⟶ U) (z : C ⟶ A)
  (hp : z ≫ p = r ≫ i) (hs : z ≫ q = s ≫ i)
  (H : IsPullback z.left r.left p.left i.left)
  (hq : IsOpenMap q.left) (hc : IsOpenMap s.left)
  {T : Scheme.{0}} (j : T ⟶ U.left) [Etale j]
set_option quotPrecheck false
local notation "m" => invariantMap e ec i.left z.left
  (congrArg Over.Hom.left hp) (congrArg Over.Hom.left hs)
local notation "O" => orbitImageOpen e hq (etaleSourceImage j)
local notation "Oc" => (TopologicalSpace.Opens.map (m).base).obj O

local notation "E" => (pullOpen e O).val
local notation "Ec" => (pullOpen ec Oc).val
local notation "g" => (openSourceMap e ec i z hp hs O).left
variable [Etale q.left] [Etale s.left]

include H hc in
/-- Generator boundary tests prove equality of the actual original invariant-sheaf sections. -/
theorem closedBoundary_eq_of_etale_tests
    (b : (invariantSheaf e).obj.obj (op O))
    (t : (invariantSheaf ec).obj.obj (op Oc))
    (h : ∀ (Z : Scheme) (a : Z ⟶ T) (w : Z ⟶ (Ec).toScheme),
      a ≫ j = w ≫ (Ec).ι ≫ i.left →
      a.appTop (etaleSourceFunctionEquiv e hq j b).val =
        w.appTop (orbitFunctions ec Oc t).val) : (m).c.app (op O) b = t := by
  apply closedBoundary_sections_ext e ec i z hp hs H hq hc j
  intro Z a w hw
  have hg : (g) ≫ (E).ι = (Ec).ι ≫ i.left := Scheme.Hom.resLE_comp_ι _ _
  have hwg : w ≫ g = a ≫ etaleOrbitImageMap e hq j := by
    apply (cancel_mono (E).ι).mp
    rw [Category.assoc, hg, Category.assoc, etaleOrbitImageMap_ι]
    exact hw.symm
  have hn := congrArg Subtype.val (openFunctionMap_natural e ec i z hp hs O b)
  calc
    w.appTop (orbitFunctions ec Oc ((m).c.app (op O) b)).val =
        (w ≫ g).appTop (orbitFunctions e O b).val := congrArg w.appTop hn.symm
    _ = a.appTop (etaleSourceFunctionEquiv e hq j b).val := by
      rw [hwg]
      exact congrArg a.appTop (etaleOrbitImageMap_appTop e hq j b)
    _ = w.appTop (orbitFunctions ec Oc t).val := h Z a w hw

end FLT.Mazur.RelativeRelationOrbit
