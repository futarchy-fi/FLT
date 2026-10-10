/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedPicardKernelPresheaf
public import FLT.Mazur.RelativePicardFppfComparison

/-!
# The normalized kernel and the relative Picard sheaf

Normalization gives a canonical locally bijective comparison. This does not
assert that the kernel is already a sheaf, nor that either functor is represented.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.SchemePicard
variable {X S : Scheme.{u}} (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)

/-- The comparison retains the underlying normalized line-bundle class. -/
def pointedFppfComparison :
    pointedKernelPresheaf f e he ⟶ (relativeFppfSheaf f).obj :=
  (relativePointedKernelIso f e he).inv ≫ relativeFppfComparison f

/-- A normalized kernel class defines a section of the relative Picard sheaf. -/
def pointedFppfClass (T : Over S) :
    (pullback (pointedBaseSection f e he T)).ker →*
      (relativeFppfSheaf f).obj.obj (op T) :=
  ((pointedFppfComparison f e he).app (op T)).hom

/-- The comparison is the original relative comparison on the underlying bundle class. -/
@[simp]
theorem pointedFppfClass_apply (T : Over S)
    (a : (pullback (pointedBaseSection f e he T)).ker) :
    pointedFppfClass f e he T a = relativeFppfClass f T
      (relativeClass (Limits.pullback.snd f T.hom) a.val) := rfl

/-- The pointed comparison commutes with the actual kernel restriction maps. -/
theorem pointedFppfClass_naturality {T U : Over S} (g : T ⟶ U)
    (a : (pullback (pointedBaseSection f e he U)).ker) :
    (relativeFppfSheaf f).obj.map g.op (pointedFppfClass f e he U a) =
      pointedFppfClass f e he T (pointedKernelMap f e he g a) :=
  ((pointedFppfComparison f e he).naturality_apply g.op a).symm

instance pointedFppfComparison_locallyInjective :
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S)
      (pointedFppfComparison f e he) := by
  unfold pointedFppfComparison
  infer_instance

instance pointedFppfComparison_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (pointedFppfComparison f e he) := by
  unfold pointedFppfComparison
  infer_instance

/-- Every Picard-sheaf section locally has a representative trivial at the chosen point. -/
theorem pointedFppfClass_locallyRepresented (T : Over S)
    (a : (relativeFppfSheaf f).obj.obj (op T)) :
    Presheaf.imageSieve (pointedFppfComparison f e he) a ∈
      (Scheme.fppfTopology.over S) T :=
  Presheaf.imageSieve_mem (Scheme.fppfTopology.over S) (pointedFppfComparison f e he) a

/-- Equality of normalized representatives in the sheaf is exactly local kernel equality. -/
theorem pointedFppfClass_eq_iff (T : Over S)
    (a b : (pullback (pointedBaseSection f e he T)).ker) :
    pointedFppfClass f e he T a = pointedFppfClass f e he T b ↔
      Presheaf.equalizerSieve (F := pointedKernelPresheaf f e he) (X := op T) a b ∈
        (Scheme.fppfTopology.over S) T := by
  constructor
  · exact Presheaf.equalizerSieve_mem (Scheme.fppfTopology.over S)
      (pointedFppfComparison f e he) a b
  · intro h
    have hs := ((sheafCompose (Scheme.fppfTopology.over S)
      (forget CommGrpCat.{u + 1})).obj (relativeFppfSheaf f)).property
    rw [isSheaf_iff_isSheaf_of_type] at hs
    apply (hs.isSeparated _ h).ext
    intro U g hg
    change (relativeFppfSheaf f).obj.map g.op (pointedFppfClass f e he T a) =
      (relativeFppfSheaf f).obj.map g.op (pointedFppfClass f e he T b)
    rw [pointedFppfClass_naturality, pointedFppfClass_naturality]
    exact congrArg (pointedFppfClass f e he U) hg

/-- Local kernel equality is equality of the actual pulled-back Picard classes. -/
theorem pointedFppfClass_equalizer_iff {T U : Over S} (g : U ⟶ T)
    (a b : (pullback (pointedBaseSection f e he T)).ker) :
    Presheaf.equalizerSieve (F := pointedKernelPresheaf f e he) (X := op T) a b g ↔
      pullback (relativeTotalMap f g) a.val = pullback (relativeTotalMap f g) b.val :=
  Subtype.ext_iff

end FLT.Mazur.SchemePicard
