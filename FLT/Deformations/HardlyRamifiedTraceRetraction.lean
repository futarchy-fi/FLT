/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedTracePoint
public import FLT.Deformations.HardlyRamifiedTraceParameters

/-!
# The trace image is a retract of the framed HR ring

Agreement on the universal trace generators proves the retraction identity.
Every trace-image coefficient map therefore extends to the framed HR ring.
No finiteness over the coefficient base is asserted.
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

/-- Maps from the actual trace image are determined by the descended traces. -/
theorem hardlyTraceMorphism_ext (A : ProartinianCat O) (f h : T ⟶ A)
    (he : ∀ g : G, f.hom (((hardlyTraceLift O hp hdim ρ hρ hirr).val g).val.trace) =
      h.hom (((hardlyTraceLift O hp hdim ρ hρ hirr).val g).val.trace)) : f = h := by
  have he' : hardlyTraceImageProjection O hp hdim ρ hρ ≫ f =
      hardlyTraceImageProjection O hp hdim ρ hρ ≫ h := by
    apply universalTraceMorphism_ext O G (Fin 2) r A
    intro g
    change f.hom ((hardlyTraceImageProjection O hp hdim ρ hρ).hom _) =
      h.hom ((hardlyTraceImageProjection O hp hdim ρ hρ).hom _)
    rw [hardlyTraceLift_trace O hp hdim ρ hρ hirr]
    exact he g
  apply ProartinianCat.hom_ext
  ext x
  obtain ⟨y, rfl⟩ := hardlyTraceImageProjection_surjective O hp hdim ρ hρ x
  exact congrArg (fun k ↦ ProartinianCat.Hom.hom k y) he'

/-- The point sends the original framed traces to the same descended traces. -/
theorem hardlyTracePoint_trace (g : G) :
    (hardlyTracePoint O hp hdim ρ hρ hirr).hom
      (((hardlyFlatLift O hp hdim ρ hρ).val g).val.trace) =
        ((hardlyTraceLift O hp hdim ρ hρ hirr).val g).val.trace := by
  rw [Matrix.trace, map_sum]
  have he : ∀ i : Fin 2, (hardlyTracePoint O hp hdim ρ hρ hirr).hom
      ((hardlyFlatLift O hp hdim ρ hρ).val g i i) =
        (hardlyTraceShearedLift O hp hdim ρ hρ hirr).val g i i :=
    fun i ↦ hardlyTracePoint_apply O hp hdim ρ hρ hirr g i i
  simp_rw [Matrix.diag_apply, he]
  exact hardlyTraceShearedLift_trace O hp hdim ρ hρ hirr g

/-- The inclusion followed by the constructed point is the identity on trace coefficients. -/
theorem hardlyTracePoint_retraction :
    inc ≫ hardlyTracePoint O hp hdim ρ hρ hirr = 𝟙 T := by
  apply hardlyTraceMorphism_ext O hp hdim ρ hρ hirr
  intro g
  change (hardlyTracePoint O hp hdim ρ hρ hirr).hom
    ((inc).hom (((hardlyTraceLift O hp hdim ρ hρ hirr).val g).val.trace)) = _
  have ht := congrArg (fun M : GL (Fin 2) H ↦ M.val.trace)
    (hardlyTraceLift_recovery O hp hdim ρ hρ hirr g)
  change Matrix.trace ((hardlyTraceFrame O hp hdim ρ hρ hirr).val *
    (((hardlyTraceLift O hp hdim ρ hρ hirr).val g).val.map (inc).hom) *
    ((hardlyTraceFrame O hp hdim ρ hρ hirr)⁻¹).val) = _ at ht
  rw [Matrix.trace_units_conj] at ht
  have hi : (inc).hom (((hardlyTraceLift O hp hdim ρ hρ hirr).val g).val.trace) =
      ((hardlyFlatLift O hp hdim ρ hρ).val g).val.trace :=
    (AddMonoidHom.map_trace (inc).hom.toRingHom.toAddMonoidHom _).trans ht
  rw [hi]
  exact hardlyTracePoint_trace O hp hdim ρ hρ hirr g

include hirr in
/-- Every continuous map on trace coefficients extends to the framed HR ring. -/
theorem hardlyTraceRestriction_surjective (A : ProartinianCat O) :
    Function.Surjective (fun f : H ⟶ A ↦ inc ≫ f) := by
  intro f
  refine ⟨hardlyTracePoint O hp hdim ρ hρ hirr ≫ f, ?_⟩
  change inc ≫ (hardlyTracePoint O hp hdim ρ hρ hirr ≫ f) = f
  rw [← Category.assoc, hardlyTracePoint_retraction, Category.id_comp]

/-- The constructed map back onto the trace image is surjective. -/
theorem hardlyTracePoint_surjective :
    Function.Surjective (hardlyTracePoint O hp hdim ρ hρ hirr).hom := by
  intro t
  exact ⟨(inc).hom t, congrArg (fun f ↦ ProartinianCat.Hom.hom f t)
    (hardlyTracePoint_retraction O hp hdim ρ hρ hirr)⟩

end Deformation
