/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedTraceArithmetic
public import FLT.Deformations.DeSmitLenstra.TraceMorphismExt

/-!
# Faithful parameterization by the actual HR trace lift

The strict recovery frame identifies the descended traces with the projected
universal traces. Consequently the descended representation determines every
coefficient map from the image ring, including maps to finite test rings.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory GaloisRepresentation
namespace Deformation
open ProartinianCat MoritaReconstruction
variable (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
  {p : ℕ} [Fact p.Prime] (hp : Odd p)
  [Algebra ℤ_[p] (residueField (𝓞 := O))] [Algebra ℤ_[p] O]
  [IsScalarTower ℤ_[p] O (residueField (𝓞 := O))]
  {V : Type} [AddCommGroup V] [Module (residueField (𝓞 := O)) V]
  [Module.Finite (residueField (𝓞 := O)) V] [Module.Free (residueField (𝓞 := O)) V]
  (hdim : Module.rank (residueField (𝓞 := O)) V = 2)
  (ρ : GaloisRep ℚ (residueField (𝓞 := O)) V) (hρ : IsHardlyRamified hp hdim ρ)
local notation "G" => Field.absoluteGaloisGroup ℚ
local notation "r" => hardlyTwoFramedResidual O hp hdim ρ hρ
local notation "H" => hardlyFlatObject O hp hdim ρ hρ
local notation "T" => hardlyTraceImageObject O hp hdim ρ hρ
local notation "inc" => hardlyTraceImageInclusion O hp hdim ρ hρ

variable (hirr : ρ.IsIrreducible)

/-- The descended trace is the image of the same universal trace generator. -/
theorem hardlyTraceLift_trace (g : G) :
    (hardlyTraceImageProjection O hp hdim ρ hρ).hom
      ⟨(profiniteUniversalMatrix O G (Fin 2) r g).trace,
        universalTrace_mem O G (Fin 2) r g⟩ =
      ((hardlyTraceLift O hp hdim ρ hρ hirr).val g).val.trace := by
  apply hardlyTraceImageInclusion_injective O hp hdim ρ hρ
  have ht := congrArg (fun M : GL (Fin 2) H ↦ M.val.trace)
    (hardlyTraceLift_recovery O hp hdim ρ hρ hirr g)
  change Matrix.trace ((hardlyTraceFrame O hp hdim ρ hρ hirr).val *
    (((hardlyTraceLift O hp hdim ρ hρ hirr).val g).val.map (inc).hom) *
    ((hardlyTraceFrame O hp hdim ρ hρ hirr)⁻¹).val) = _ at ht
  rw [Matrix.trace_units_conj] at ht
  exact (traceSpecialization_trace O G (Fin 2) r H
    (hardlyFlatLift O hp hdim ρ hρ) g).trans
      ((AddMonoidHom.map_trace (inc).hom.toRingHom.toAddMonoidHom
        ((hardlyTraceLift O hp hdim ρ hρ hirr).val g).val).trans ht).symm

/-- A coefficient map specializes the constructed representation on the trace image. -/
def hardlyTraceParameterRepresentation (A : ProartinianCat O) (f : T ⟶ A) :
    G →ₜ* GL (Fin 2) A :=
  (repnFunctor (Fin 2) G O).map f (hardlyTraceLift O hp hdim ρ hρ hirr).val

/-- Specializing the representation loses no information about its coefficient map. -/
theorem hardlyTraceParameterRepresentation_injective (A : ProartinianCat O) :
    Function.Injective (hardlyTraceParameterRepresentation O hp hdim ρ hρ hirr A) := by
  intro f h he
  have he' : hardlyTraceImageProjection O hp hdim ρ hρ ≫ f =
      hardlyTraceImageProjection O hp hdim ρ hρ ≫ h := by
    apply universalTraceMorphism_ext O G (Fin 2) r A
    intro g
    change f.hom ((hardlyTraceImageProjection O hp hdim ρ hρ).hom _) =
      h.hom ((hardlyTraceImageProjection O hp hdim ρ hρ).hom _)
    rw [hardlyTraceLift_trace O hp hdim ρ hρ hirr]
    have ht := congrArg (fun t : G →ₜ* GL (Fin 2) A ↦ (t g).val.trace) he
    exact (AddMonoidHom.map_trace f.hom.toRingHom.toAddMonoidHom _).trans
      (ht.trans (AddMonoidHom.map_trace h.hom.toRingHom.toAddMonoidHom _).symm)
  apply ProartinianCat.hom_ext
  ext x
  obtain ⟨y, rfl⟩ := hardlyTraceImageProjection_surjective O hp hdim ρ hρ x
  exact congrArg (fun k ↦ ProartinianCat.Hom.hom k y) he'

/-- Every specialization retains trivial arithmetic inertia away from 2p. -/
theorem hardlyTraceParameterRepresentation_inertia (A : ProartinianCat O) (f : T ⟶ A)
    (g : G) (hg : g ∈ hardlyAwayInertia p) :
    hardlyTraceParameterRepresentation O hp hdim ρ hρ hirr A f g = 1 := by
  change Matrix.GeneralLinearGroup.map f.hom.toRingHom
    ((hardlyTraceLift O hp hdim ρ hρ hirr).val g) = 1
  rw [hardlyTraceLift_inertia O hp hdim ρ hρ hirr g hg, map_one]

end Deformation
