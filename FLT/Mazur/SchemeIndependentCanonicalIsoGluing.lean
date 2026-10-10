/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeIndependentCanonicalFullyFaithful

/-!
# Gluing the specified isomorphisms of line bundles

Compatible isomorphisms on the original members lift uniquely. Their inverses
satisfy the reversed original pair equations, so the lift is an isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeFppfFamily.IndependentLineData
open SchemePicard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} {𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X}

/-- Compatible original member isomorphisms define an independent-data isomorphism. -/
def isoMk {D E : IndependentLineData 𝒰}
    (a : ∀ i, (D.obj i).val ≅ (E.obj i).val)
    (ha : PairMapCompatible 𝒰 D.overlap E.overlap (fun i ↦ (a i).hom)) : D ≅ E where
  hom := ⟨fun i ↦ (a i).hom, ha⟩
  inv := ⟨fun i ↦ (a i).inv, fun ij ↦ by
    apply (cancel_epi ((pullback (Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2))).map
      (a ij.1).hom)).mp
    rw [← Category.assoc, ← ha ij]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id, ← Functor.map_comp_assoc,
      Category.id_comp]⟩
  hom_inv_id := hom_ext (fun i ↦ (a i).hom_inv_id)
  inv_hom_id := hom_ext (fun i ↦ (a i).inv_hom_id)

variable (𝒰)

/-- Glue the supplied original compatible isomorphisms between base line bundles. -/
def glueIso {L K : LineBundleCat X}
    (a : ∀ i, (pullback (𝒰.f i)).obj L.val ≅ (pullback (𝒰.f i)).obj K.val)
    (ha : PairMapCompatible 𝒰 (canonicalObj 𝒰 L).overlap (canonicalObj 𝒰 K).overlap
      (fun i ↦ (a i).hom)) : L.val ≅ K.val :=
  (lineBundleForget X).mapIso ((canonical 𝒰).preimageIso (isoMk a ha))

/-- The glued isomorphism restricts to each supplied original isomorphism. -/
lemma glueIso_member {L K : LineBundleCat X}
    (a : ∀ i, (pullback (𝒰.f i)).obj L.val ≅ (pullback (𝒰.f i)).obj K.val)
    (ha : PairMapCompatible 𝒰 (canonicalObj 𝒰 L).overlap (canonicalObj 𝒰 K).overlap
      (fun i ↦ (a i).hom)) (i : 𝒰.I₀) :
    (pullback (𝒰.f i)).map (glueIso 𝒰 a ha).hom = (a i).hom := by
  exact canonical_preimage_member 𝒰 (L := L) (K := K)
    (isoMk (D := canonicalObj 𝒰 L) (E := canonicalObj 𝒰 K) a ha).hom i

/-- Agreement on every original member determines a global line bundle map. -/
lemma hom_ext_of_members {L K : LineBundleCat X} {a b : L.val ⟶ K.val}
    (h : ∀ i, (pullback (𝒰.f i)).map a = (pullback (𝒰.f i)).map b) : a = b := by
  have hh : (InducedCategory.homMk a : L ⟶ K) = InducedCategory.homMk b :=
    (canonical 𝒰).map_injective (hom_ext h)
  exact congrArg (fun c ↦ c.hom) hh

end FLT.Mazur.SchemeFppfFamily.IndependentLineData
