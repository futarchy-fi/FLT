/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.FlatReductionIdeal
public import FLT.Deformations.RepresentationTheory.FlatFramedChange

/-!
# Effectivity of the closed finite-flat quotient

The universal representation on the quotient by `flatReductionIdeal` is
flat at the given place. Every open reduction comes from a finite-flat open
reduction of the original ring; the coefficient comparison is constructed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NumberField CategoryTheory
namespace Deformation
open ProartinianCat
variable {O : Type} [CommRing O] [IsLocalRing O]
  [Finite (IsLocalRing.ResidueField O)] (U : ProartinianCat O)
  {K : Type} [Field K] [NumberField K] {n : Type} [Fintype n] [DecidableEq n]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ρ : FramedGaloisRep K U n)
  (hex : (flatReductionIdeals U v ρ).Nonempty)
  (hne : flatReductionIdeal U v ρ ≠ ⊤)

/-- The actual proartinian quotient imposing the closed flat-reduction ideal. -/
def flatClosedObject : ProartinianCat O :=
  closedIdealQuotient U (flatReductionIdeal U v ρ) (flatReductionIdeal_closed U v ρ) hne

/-- Its canonical continuous coefficient projection. -/
def flatClosedProjection : U ⟶ flatClosedObject U v ρ hne :=
  closedIdealQuotientHom U (flatReductionIdeal U v ρ) (flatReductionIdeal_closed U v ρ) hne

/-- The representation on this quotient is obtained by its actual coefficient map. -/
def flatClosedRepresentation : FramedGaloisRep K (flatClosedObject U v ρ hne) n :=
  ρ.baseChange (flatClosedProjection U v ρ hne).hom.toRingHom
    (flatClosedProjection U v ρ hne).hom.cont

include hex in
/-- All open reductions of the constructed quotient have finite-flat models. -/
theorem flatClosedRepresentation_isFlat :
    (flatClosedRepresentation U v ρ hne).IsFlatAt v := by
  constructor
  intro J hJ
  let Q := flatClosedObject U v ρ hne
  let π := (flatClosedProjection U v ρ hne).hom.toRingHom
  let I := J.comap π
  have hIopen : IsOpen (I : Set U) :=
    hJ.preimage (flatClosedProjection U v ρ hne).hom.cont
  have hle : flatReductionIdeal U v ρ ≤ I := by
    intro x hx
    change Ideal.Quotient.mk (flatReductionIdeal U v ρ) x ∈ J
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact J.zero_mem
  have hflat := (flatReductionIdeal_le_iff U v ρ hex hIopen).mp hle
  let f : U →+* Q ⧸ J := (Ideal.Quotient.mk J).comp π
  let g : (U ⧸ I) →+* Q ⧸ J := Ideal.Quotient.lift I f (by
    intro x hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx)
  have hgcont : Continuous g :=
    (QuotientRing.isOpenQuotientMap_mk I).isQuotientMap.continuous_iff.mpr
      (continuous_quot_mk.comp (flatClosedProjection U v ρ hne).hom.cont)
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk I x, rfl⟩
  have hsource := (FramedGaloisRep.hasFlatProlongationAt_baseChange_iff v ρ).mp hflat
  have htarget := FramedGaloisRep.hasFlatProlongationAt_of_surjective v
    (ρ.baseChange (Ideal.Quotient.mk I) continuous_quot_mk) g hgcont hgsurj hsource
  apply (FramedGaloisRep.hasFlatProlongationAt_baseChange_iff v
    (flatClosedRepresentation U v ρ hne)).mpr
  convert htarget using 1
  apply FramedGaloisRep.GL.injective
  ext s i j
  simp only [flatClosedRepresentation, FramedGaloisRep.baseChange_GL]
  rfl

end Deformation
