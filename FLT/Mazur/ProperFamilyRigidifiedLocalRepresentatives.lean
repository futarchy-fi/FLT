/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyRigidifiedComparisons
public import FLT.Mazur.RigidifiedPicardFppfComparison

/-!
# Actual local representatives and unique local comparisons

Membership in the covering image sieve supplies a genuine line bundle and
trivialization. On the equality sieve of a proper family, the original pulled
bundles have a unique isomorphism preserving their transported trivializations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.SchemePicard
open FCurve.LineSheafSectionRigidity

/-- The image sieve can be stated using actual bundles, rather than quotient elements. -/
theorem rigidifiedFppfClass_image_iff {X S : Scheme.{u}} (f : X ⟶ S)
    (e : S ⟶ X) (he : e ≫ f = 𝟙 S) {T U : Over S} (g : U ⟶ T)
    (a : (relativeFppfSheaf f).obj.obj (op T)) :
    Presheaf.imageSieve (rigidifiedFppfComparison f e he) a g ↔
      ∃ L : RigidifiedBundle (pointedBaseSection f e he U),
        relativeFppfClass f U (relativeClass (Limits.pullback.snd f U.hom)
          (mk L.1.val L.1.property)) = (relativeFppfSheaf f).obj.map g.op a := by
  change (∃ b : RigidifiedPic (pointedBaseSection f e he U),
    rigidifiedFppfClass f e he U b = (relativeFppfSheaf f).obj.map g.op a) ↔ _
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨L, rfl⟩ := Quotient.exists_rep b
    exact ⟨L, hb⟩
  · rintro ⟨L, hL⟩
    exact ⟨Quotient.mk _ L, hL⟩

variable {X S : Scheme.{0}} [IsLocallyNoetherian S]
  (f : X ⟶ S) [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]
  (e : S ⟶ X) (he : e ≫ f = 𝟙 S)

/-- Local equality has a unique comparison of the original pulled rigidified bundles. -/
theorem pointedFamily_equalizer_unique_iff {T U : Over S} (g : U ⟶ T)
    (L M : RigidifiedBundle (pointedBaseSection f e he T)) :
    let L' := rigidifiedBundlePullback _ _ (relativeTotalMap f g) g.left
      (pointedBaseSection_naturality f e he g) L
    let M' := rigidifiedBundlePullback _ _ (relativeTotalMap f g) g.left
      (pointedBaseSection_naturality f e he g) M
    Presheaf.equalizerSieve (F := rigidifiedPresheaf f e he) (X := op T)
        (Quotient.mk _ L) (Quotient.mk _ M) g ↔
      ∃! i : L'.1.val ≅ M'.1.val,
        (Scheme.Modules.pullback (pointedBaseSection f e he U)).map i.hom ≫ M'.2.hom =
          L'.2.hom := by
  dsimp only
  rw [rigidifiedFppfClass_equalizer_iff]
  constructor
  · rintro ⟨i⟩
    exact existsUnique_rigidifiedIso (Limits.pullback.snd f U.hom) _
      (pointedBaseSection_snd f e he U) (L.1.property.pullback (relativeTotalMap f g))
      (pointedFamily_appTop_surjective f e he U) _ _ i.val
  · rintro ⟨i, hi, _⟩
    exact ⟨⟨i, hi⟩⟩

end FLT.Mazur.SchemePicard
