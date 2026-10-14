/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertRelationOperations

/-!
# The original relation on invariant translation fibers

When the original translation coordinate is invariant, its open envelope
forces both endpoints to agree. Reflexivity then proves that each endpoint
is an isomorphism. This uses the original relation over the unchanged ground;
it does not replace that ground by the translation coefficient ring.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "β" => k ≫ variableHilbertBase f d V
local notation "e" => equivalence f hL d V c k

/-- Envelope monicity distinguishes arrows with the same invariant translation coordinate. -/
theorem translationInvariant_snd_mono (hb : p ≫ β = q ≫ β) : Mono q := by
  let _ : Mono (toEnvelope f hL d V c k) := Over.mono_of_mono_left _
  constructor
  intro T a b hab
  apply (cancel_mono (toEnvelope f hL d V c k)).mp
  apply prod.hom_ext
  · simpa only [Category.assoc, toEnvelope_test] using hab
  · simp only [Category.assoc, toEnvelope_base]
    rw [hb, ← Category.assoc, hab, Category.assoc]

/-- Reflexivity makes the original second endpoint invertible on this translation slice. -/
theorem translationInvariant_snd_isIso (hb : p ≫ β = q ≫ β) : IsIso q := by
  let _ := translationInvariant_snd_mono f hL d V c k hb
  let _ : IsSplitEpi q := IsSplitEpi.mk' ⟨(e).r, (e).reflexivity₂⟩
  exact isIso_of_mono_of_isSplitEpi q

/-- The original full relation is diagonal when its translation coordinate is invariant. -/
theorem translationInvariant_endpoints (hb : p ≫ β = q ≫ β) : p = q := by
  let _ := translationInvariant_snd_isIso f hL d V c k hb
  have hh : (e).r = inv q := by
    apply (cancel_mono q).mp
    rw [(e).reflexivity₂, IsIso.inv_hom_id]
  calc
    p = q ≫ (e).r ≫ p := by rw [hh, IsIso.hom_inv_id_assoc]
    _ = q := by rw [(e).reflexivity₁, Category.comp_id]

/-- Reflexivity now supplies invariant actual original representative arrows. -/
theorem translationInvariant_representatives (hb : p ≫ β = q ≫ β) :
    (p).left ≫ (e).r.left ≫ (q).left = (q).left ≫ (e).r.left ≫ (q).left := by
  exact congrArg (fun t : relation f hL d V c k ⟶ A ↦
    t.left ≫ (e).r.left ≫ (q).left) (translationInvariant_endpoints f hL d V c k hb)

end FLT.Mazur.HilbertChart.AffineRestriction
