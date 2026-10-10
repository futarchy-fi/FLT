/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RigidifiedPicardPresheaf
public import FLT.Mazur.PointedPicardFppfComparison

/-!
# Local comparison with actual rigidified Picard classes

The canonical comparison is locally bijective. Its local equality relation
uses actual isomorphisms preserving the transported trivializations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.SchemePicard
open FCurve.LineSheafSectionRigidity
variable {X S : Scheme.{u}} (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)

/-- The comparison from actual rigidified classes to the relative Picard sheaf. -/
def rigidifiedFppfComparison :
    rigidifiedPresheaf f e he ⟶ (relativeFppfSheaf f).obj ⋙ forget CommGrpCat :=
  (rigidifiedPresheafKernelIso f e he).hom ≫
    Functor.whiskerRight (pointedFppfComparison f e he) (forget CommGrpCat)

/-- The Picard-sheaf section of a rigidified class. -/
def rigidifiedFppfClass (T : Over S)
    (a : RigidifiedPic (pointedBaseSection f e he T)) :
    (relativeFppfSheaf f).obj.obj (op T) :=
  (rigidifiedFppfComparison f e he).app (op T) a

/-- The comparison retains the kernel class of the actual rigidified bundle. -/
theorem rigidifiedFppfClass_apply (T : Over S)
    (a : RigidifiedPic (pointedBaseSection f e he T)) :
    rigidifiedFppfClass f e he T a =
      pointedFppfClass f e he T (rigidifiedKernel (pointedBaseSection f e he T) a) := rfl

instance rigidifiedFppfComparison_locallyInjective :
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S)
      (rigidifiedFppfComparison f e he) := by
  unfold rigidifiedFppfComparison
  infer_instance

instance rigidifiedFppfComparison_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (rigidifiedFppfComparison f e he) := by
  unfold rigidifiedFppfComparison
  infer_instance

/-- Every Picard-sheaf section is locally represented by actual rigidified bundle classes. -/
theorem rigidifiedFppfClass_locallyRepresented (T : Over S)
    (a : (relativeFppfSheaf f).obj.obj (op T)) :
    Presheaf.imageSieve (rigidifiedFppfComparison f e he) a ∈
      (Scheme.fppfTopology.over S) T :=
  Presheaf.imageSieve_mem (Scheme.fppfTopology.over S) (rigidifiedFppfComparison f e he) a

/-- Equality in the Picard sheaf is local equality of rigidified isomorphism classes. -/
theorem rigidifiedFppfClass_eq_iff (T : Over S)
    (a b : RigidifiedPic (pointedBaseSection f e he T)) :
    rigidifiedFppfClass f e he T a = rigidifiedFppfClass f e he T b ↔
      Presheaf.equalizerSieve (F := rigidifiedPresheaf f e he) (X := op T) a b ∈
        (Scheme.fppfTopology.over S) T := by
  rw [rigidifiedFppfClass_apply, rigidifiedFppfClass_apply, pointedFppfClass_eq_iff]
  apply Iff.of_eq
  congr 1
  ext U g
  change pointedKernelMap f e he g (rigidifiedKernel _ a) =
      pointedKernelMap f e he g (rigidifiedKernel _ b) ↔
    rigidifiedBaseMap f e he g a = rigidifiedBaseMap f e he g b
  rw [← rigidifiedBaseMap_kernel, ← rigidifiedBaseMap_kernel]
  exact (rigidifiedKernel_injective _ (Limits.pullback.snd f U.hom)
    (pointedBaseSection_snd f e he U)).eq_iff

/-- The equality sieve uses actual isomorphisms preserving pulled rigidifications. -/
theorem rigidifiedFppfClass_equalizer_iff {T U : Over S} (g : U ⟶ T)
    (L M : RigidifiedBundle (pointedBaseSection f e he T)) :
    Presheaf.equalizerSieve (F := rigidifiedPresheaf f e he) (X := op T)
      (Quotient.mk _ L) (Quotient.mk _ M) g ↔
      Nonempty (RigidifiedIso (pointedBaseSection f e he U)
        (rigidifiedBundlePullback _ _ (relativeTotalMap f g) g.left
          (pointedBaseSection_naturality f e he g) L).2
        (rigidifiedBundlePullback _ _ (relativeTotalMap f g) g.left
          (pointedBaseSection_naturality f e he g) M).2) := Quotient.eq

end FLT.Mazur.SchemePicard
