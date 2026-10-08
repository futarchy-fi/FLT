/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePicardFppfSheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Local comparison with relative Picard classes

Every section of the Picard sheaf is locally represented by a relative class.
Equality of represented sections is exactly local equality of relative classes;
on line-bundle representatives this is tensoring by a bundle from the base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.SchemePicard
local instance : Limits.HasColimitsOfSize.{u + 1, u + 1} CommGrpCat.{u + 1} :=
  Adjunction.has_colimits_of_equivalence commGroupAddCommGroupEquivalence.functor
variable {X S : Scheme.{u}} (f : X ⟶ S)

instance relativeFppfComparison_locallyInjective :
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) (relativeFppfComparison f) :=
  inferInstanceAs (Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S)
    (toSheafify (Scheme.fppfTopology.over S) (relativePresheaf f)))

instance relativeFppfComparison_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (relativeFppfComparison f) :=
  inferInstanceAs (Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
    (toSheafify (Scheme.fppfTopology.over S) (relativePresheaf f)))

/-- A Picard-sheaf section has relative-class representatives on a covering sieve. -/
lemma relativeFppfClass_locallyRepresented (T : Over S)
    (s : (relativeFppfSheaf f).obj.obj (op T)) :
    Presheaf.imageSieve (relativeFppfComparison f) s ∈ (Scheme.fppfTopology.over S) T :=
  Presheaf.imageSieve_mem (Scheme.fppfTopology.over S) (relativeFppfComparison f) s

/-- Equality in the Picard sheaf is detected by local equality of relative classes. -/
lemma relativeFppfClass_eq_iff (T : Over S)
    (a b : RelativePic (Limits.pullback.snd f T.hom)) :
    relativeFppfClass f T a = relativeFppfClass f T b ↔
      Presheaf.equalizerSieve (F := relativePresheaf f) (X := op T) a b ∈
        (Scheme.fppfTopology.over S) T := by
  constructor
  · exact Presheaf.equalizerSieve_mem (Scheme.fppfTopology.over S)
      (relativeFppfComparison f) a b
  · intro h
    have hs := ((sheafCompose (Scheme.fppfTopology.over S)
      (forget CommGrpCat.{u + 1})).obj (relativeFppfSheaf f)).property
    rw [isSheaf_iff_isSheaf_of_type] at hs
    apply (hs.isSeparated _ h).ext
    intro U g hg
    change (relativeFppfSheaf f).obj.map g.op (relativeFppfClass f T a) =
      (relativeFppfSheaf f).obj.map g.op (relativeFppfClass f T b)
    rw [relativeFppfClass_naturality, relativeFppfClass_naturality]
    exact congrArg (relativeFppfClass f U) hg

/-- Local equality of representatives is precisely a base twist on that test scheme. -/
lemma relativeFppfClass_equalizer_iff (T U : Over S) (g : U ⟶ T)
    (a b : Pic (Limits.pullback f T.hom)) :
    Presheaf.equalizerSieve (F := relativePresheaf f) (X := op T)
        (relativeClass (Limits.pullback.snd f T.hom) a)
        (relativeClass (Limits.pullback.snd f T.hom) b) g ↔
      ∃ c : Pic U.left, pullback (Limits.pullback.snd f U.hom) c =
        (pullback (relativeTotalMap f g) a)⁻¹ * pullback (relativeTotalMap f g) b := by
  change relativeClass (Limits.pullback.snd f U.hom) (pullback (relativeTotalMap f g) a) =
    relativeClass (Limits.pullback.snd f U.hom) (pullback (relativeTotalMap f g) b) ↔ _
  exact relativeClass_eq_iff _ _ _

end FLT.Mazur.SchemePicard
