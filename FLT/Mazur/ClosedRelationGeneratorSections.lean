/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedRelationGeneratorImages
public import FLT.Mazur.RelativeRelationEtaleOrbitImageMap
public import FLT.Mazur.RelativeRelationOpenFunctionMap

/-!
# Boundary invariant sections detected by an unsaturated etale generator

The boundary fiber product generates the full inverse-image orbit domain.
Its function comparison is injective even when the generator does not cover
the saturated source. Equality on scheme-valued boundary tests therefore
detects equality of the original invariant sections, including nilpotents.
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

include H in
/-- The actual invariant-sheaf boundary domain is the orbit image of the fiber product. -/
theorem boundaryGenerator_invariantOrbitImage :
    orbitImageOpen ec hc (etaleSourceImage (pullback.snd j i.left)) = Oc := by
  have hb : ⇑(m).base = closedOrbitMap e ec i z hp hs := by
    ext v
    obtain ⟨b, rfl⟩ := projection_surjective ec v
    exact invariantMap_projection_apply e ec i.left z.left _ _ b
  apply TopologicalSpace.Opens.ext
  change _ = (m).base ⁻¹' (O : Set (Orbit e))
  rw [hb, boundaryGenerator_orbitImage e ec i z hp hs H hq hc j]

variable [Etale s.left]

/-- Scheme tests over the generator detect all invariant functions on its boundary orbit image. -/
theorem boundaryGenerator_sections_ext
    (W : TopologicalSpace.Opens (Orbit ec))
    (hW : orbitImageOpen ec hc (etaleSourceImage (pullback.snd j i.left)) = W)
    (t₁ t₂ : (invariantSheaf ec).obj.obj (op W))
    (h : ∀ (Z : Scheme) (a : Z ⟶ T) (b : Z ⟶ (pullOpen ec W).val.toScheme),
      a ≫ j = b ≫ (pullOpen ec W).val.ι ≫ i.left →
      b.appTop (orbitFunctions ec W t₁).val =
        b.appTop (orbitFunctions ec W t₂).val) : t₁ = t₂ := by
  subst W
  let b := etaleOrbitImageMap ec hc (pullback.snd j i.left)
  apply (etaleSourceFunctionEquiv ec hc (pullback.snd j i.left)).injective
  apply Subtype.ext
  rw [← etaleOrbitImageMap_appTop, ← etaleOrbitImageMap_appTop]
  apply h (pullback j i.left) (pullback.fst j i.left) b
  rw [← Category.assoc, etaleOrbitImageMap_ι]
  exact pullback.condition

include H hc in
/-- Boundary tests of any etale generator detect sections on the whole original boundary. -/
theorem closedBoundary_sections_ext
    (t₁ t₂ : (invariantSheaf ec).obj.obj (op Oc))
    (h : ∀ (Z : Scheme) (a : Z ⟶ T) (b : Z ⟶ (pullOpen ec Oc).val.toScheme),
      a ≫ j = b ≫ (pullOpen ec Oc).val.ι ≫ i.left →
      b.appTop (orbitFunctions ec Oc t₁).val =
        b.appTop (orbitFunctions ec Oc t₂).val) : t₁ = t₂ :=
  boundaryGenerator_sections_ext ec i hc j Oc
    (boundaryGenerator_invariantOrbitImage e ec i z hp hs H hq hc j) t₁ t₂ h

end FLT.Mazur.RelativeRelationOrbit
