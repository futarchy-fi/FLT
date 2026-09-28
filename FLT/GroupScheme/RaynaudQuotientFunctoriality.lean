/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudFlatQuotient
public import FLT.GroupScheme.RaynaudRankThreeExtension

/-!
# Functoriality of contracted finite flat quotients

An integral morphism that induces a morphism of the prescribed generic
quotients descends to their contracted integral models. Over the three-adic
integers, the descended map is an isomorphism when both quotients have order
three and the generic quotient map is surjective.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
    [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]
    {X X' Y Y' : FF R K}

omit [IsDedekindDomain R] [IsFractionRing R K] in
/-- A compatible integral map preserves the contracted quotient subalgebras. -/
theorem GenericGaloisHom.map_mem_quotientCoordinates
    (q : GenericGaloisHom X Y) (q' : GenericGaloisHom X' Y')
    (g : ModelHom X X') (h : GenericGaloisHom Y Y')
    (hc : q'.comp (genericHom g) = h.comp q) (a : q'.quotientCoordinates) :
    g a.val ∈ q.quotientCoordinates := by
  obtain ⟨b, hb⟩ := a.property
  change q'.toBialgHom b = 1 ⊗ₜ[R] a.val at hb
  refine ⟨h.toBialgHom b, ?_⟩
  have he := congrArg (GenericGaloisHom.toBialgHom (X := X) (Y := Y')) hc
  rw [GenericGaloisHom.toBialgHom_comp, GenericGaloisHom.toBialgHom_comp,
    ModelHom.toBialgHom_genericHom] at he
  change q.toBialgHom (h.toBialgHom b) = 1 ⊗ₜ[R] g a.val
  calc
    q.toBialgHom (h.toBialgHom b) = g.baseChange (q'.toBialgHom b) :=
      (DFunLike.congr_fun he b).symm
    _ = 1 ⊗ₜ[R] g a.val := by rw [hb]; rfl

/-- Restrict an integral morphism to the coordinate rings of compatible quotients. -/
def GenericGaloisHom.quotientCoordinateMap
    (q : GenericGaloisHom X Y) (q' : GenericGaloisHom X' Y')
    (g : ModelHom X X') (h : GenericGaloisHom Y Y')
    (hc : q'.comp (genericHom g) = h.comp q) :
    q'.quotientCoordinates →ₐc[R] q.quotientCoordinates :=
  BialgHom.factorOfInjectiveOfFlat q.quotientInclusion Subtype.val_injective
    (g.comp q'.quotientInclusion)
    ((g.toAlgHom.comp q'.quotientCoordinates.val).codRestrict q.quotientCoordinates
      (q.map_mem_quotientCoordinates q' g h hc)) (by ext; rfl)

/-- An integral morphism descends to its compatible contracted generic quotients. -/
def GenericGaloisHom.flatQuotientMap
    (q : GenericGaloisHom X Y) (q' : GenericGaloisHom X' Y')
    (hq : Function.Surjective q) (hq' : Function.Surjective q')
    (g : ModelHom X X') (h : GenericGaloisHom Y Y')
    (hc : q'.comp (genericHom g) = h.comp q) :
    ModelHom (q.flatQuotient hq) (q'.flatQuotient hq') :=
  q.quotientCoordinateMap q' g h hc

/-- The descended integral map commutes with the quotient projections. -/
@[simp] theorem GenericGaloisHom.toFlatQuotient_comp_flatQuotientMap
    (q : GenericGaloisHom X Y) (q' : GenericGaloisHom X' Y')
    (hq : Function.Surjective q) (hq' : Function.Surjective q')
    (g : ModelHom X X') (h : GenericGaloisHom Y Y')
    (hc : q'.comp (genericHom g) = h.comp q) :
    (q.toFlatQuotient hq).comp (q.flatQuotientMap q' hq hq' g h hc) =
      g.comp (q'.toFlatQuotient hq') := by
  ext a
  rfl

/-- The descended map induces the prescribed morphism of generic quotients. -/
@[simp] theorem GenericGaloisHom.genericHom_flatQuotientMap
    (q : GenericGaloisHom X Y) (q' : GenericGaloisHom X' Y')
    (hq : Function.Surjective q) (hq' : Function.Surjective q')
    (g : ModelHom X X') (h : GenericGaloisHom Y Y')
    (hc : q'.comp (genericHom g) = h.comp q) (y : Y.Points) :
    genericHom (q.flatQuotientMap q' hq hq' g h hc) y = h y := by
  obtain ⟨x, rfl⟩ := hq y
  have he := congrArg (fun k : ModelHom X (q'.flatQuotient hq') ↦ genericHom k x)
    (q.toFlatQuotient_comp_flatQuotientMap q' hq hq' g h hc)
  simp only [genericHom_comp, GenericGaloisHom.genericHom_toFlatQuotient] at he
  exact he.trans (DFunLike.congr_fun hc x)

/-- A generically surjective quotient comparison is injective on integral coordinates. -/
theorem GenericGaloisHom.flatQuotientMap_injective
    (q : GenericGaloisHom X Y) (q' : GenericGaloisHom X' Y')
    (hq : Function.Surjective q) (hq' : Function.Surjective q')
    (g : ModelHom X X') (h : GenericGaloisHom Y Y')
    (hc : q'.comp (genericHom g) = h.comp q) (hh : Function.Surjective h) :
    Function.Injective (q.flatQuotientMap q' hq hq' g h hc) := by
  apply ModelHom.injective_of_baseChange_injective
  rw [← ModelHom.toBialgHom_genericHom]
  apply GenericGaloisHom.toBialgHom_injective
  intro y
  obtain ⟨x, rfl⟩ := hh y
  exact ⟨x, q.genericHom_flatQuotientMap q' hq hq' g h hc x⟩

/-- Order-three rigidity makes the integral comparison of quotient models an isomorphism. -/
theorem GenericGaloisHom.flatQuotientMap_bijective_of_order_three
    {X X' Y Y' : FF ℤ_[3] ℚ_[3]}
    (q : GenericGaloisHom X Y) (q' : GenericGaloisHom X' Y')
    (hq : Function.Surjective q) (hq' : Function.Surjective q')
    (g : ModelHom X X') (h : GenericGaloisHom Y Y')
    (hc : q'.comp (genericHom g) = h.comp q) (hh : Function.Surjective h)
    (hY : Nat.card Y.Points = 3) (hY' : Nat.card Y'.Points = 3) :
    Function.Bijective (q.flatQuotientMap q' hq hq' g h hc) := by
  have hi := q.flatQuotientMap_injective q' hq hq' g h hc hh
  exact ⟨hi, raynaud_integral_rigidity_of_order_three
    (q'.flatQuotient hq') (q.flatQuotient hq) hY' hY _ hi⟩

end ThreeAdicPlan
