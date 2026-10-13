/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFullFiberInterior
public import FLT.Mazur.AffineHilbertNestedRestriction

/-!
# Retaining a full fiber under whole-orbit source restriction

An actual open source restriction retaining all endpoints over a chosen point
retains its full independent envelope fiber. The proof lifts original arrows
through both pullbacks and uses the monic product map to preserve residue
branches. The restricted full-fiber locus is not asserted to be open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  {B : Over (Spec (.of R))} (v : B ⟶ A)
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "j" => Over.Hom.left (toEnvelope f hL d V c k)
local notation "j'" => Over.Hom.left (toEnvelope f hL d V c (v ≫ k))
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "π'" => Over.Hom.left (prod.fst : prod B V ⟶ B)

/-- Every original arrow whose two endpoints lift has a point on the full nested relation. -/
theorem nestedRelation_exists_point (z : (relation f hL d V c k).left)
    (hp : (p).left z ∈ Set.range v.left) (hq : (q).left z ∈ Set.range v.left) :
    ∃ w : (relation f hL d V c (v ≫ k)).left,
      (nestedToFullRelation f hL d V c k v).left w = z := by
  obtain ⟨x, hx⟩ := hp
  obtain ⟨y, hy⟩ := hq
  obtain ⟨a, ha, _⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback (p).left v.left) z x hx.symm
  have hq' : (pullback.fst (p).left v.left ≫ (q).left) a = v.left y := by
    change (q).left (pullback.fst (p).left v.left a) = v.left y
    rw [ha, hy]
  obtain ⟨b, hb, _⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback (pullback.fst (p).left v.left ≫ (q).left) v.left) a y hq'
  let e := nestedSchemeDoubleIso f hL d V c k v
  refine ⟨e.inv b, ?_⟩
  have he := nestedSchemeDoubleIso_arrow f hL d V c k v
  change e.hom ≫ SchemeRelationRestriction.arrow (p).left (q).left v.left = _ at he
  rw [← he]
  change (e.inv ≫ e.hom ≫ SchemeRelationRestriction.arrow (p).left (q).left v.left) b = z
  rw [e.inv_hom_id_assoc]
  change (pullback.fst (p).left v.left)
    ((pullback.fst (pullback.fst (p).left v.left ≫ (q).left) v.left) b) = z
  rw [hb, ha]

variable [IsOpenImmersion k.left] [IsOpenImmersion v.left]

instance nestedOpenChart_isOpenImmersion : IsOpenImmersion (v ≫ k).left := by
  change IsOpenImmersion (v.left ≫ k.left)
  infer_instance

/-- Whole-orbit restriction preserves every independent branch over the retained point. -/
theorem nested_fullFiber_retained (x : B.left)
    (hx : v.left x ∈ fullEnvelopeLocus f hL d V c k)
    (horbit : ∀ z : (relation f hL d V c k).left,
      (q).left z = v.left x → (p).left z ∈ Set.range v.left) :
    x ∈ fullEnvelopeLocus f hL d V c (v ≫ k) := by
  apply (mem_fullFiberLocus π' (j').opensRange x).mpr
  intro y hy
  have hp : π ((prod.map v (𝟙 V)).left y) = v.left x := by
    change ((prod.map v (𝟙 V)).left ≫ π) y = _
    rw [← Over.comp_left, prod.map_fst]
    change v.left (π' y) = v.left x
    rw [hy]
  obtain ⟨z, hz⟩ := (mem_fullFiberLocus π (j).opensRange _).mp hx _ hp
  have hq : (q).left z = v.left x := by
    rw [← toEnvelope_test f hL d V c k]
    change π ((j) z) = v.left x
    rw [hz]
    exact hp
  obtain ⟨w, hw⟩ := nestedRelation_exists_point f hL d V c k v z
    (horbit z hq) ⟨x, hq.symm⟩
  have hm : IsOpenImmersion (prod.map v (𝟙 V)).left :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_prod_fst_with_id v V).map (Over.forget _))
      (inferInstanceAs (IsOpenImmersion v.left))
  let _ := hm
  refine ⟨w, (prod.map v (𝟙 V)).left.injective ?_⟩
  change ((toEnvelope f hL d V c (v ≫ k) ≫ prod.map v (𝟙 V)).left) w = _
  rw [← nestedToFullRelation_envelope]
  change (j) ((nestedToFullRelation f hL d V c k v).left w) = _
  rw [hw, hz]

end FLT.Mazur.HilbertChart.AffineRestriction
