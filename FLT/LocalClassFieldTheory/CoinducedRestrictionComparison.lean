/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CoinducedInjectiveRestriction
public import FLT.LocalClassFieldTheory.CoinducedTateShift

/-!
# Comparing the restricted dimension shift with the subgroup construction

Restrict functions on G to H and descend this map to the two coefficient
quotients. Although those quotients need not be isomorphic as representations,
the resulting map induces isomorphisms on Tate cohomology in every degree.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

variable {k G H : Type} [CommRing k] [Group G] [Group H]
  (M : Rep.{0} k G) (f : H →* G)

/-- Restrict a coinduced function along a group homomorphism. -/
def coinducedRestriction : Rep.res f (coinducedCoefficients M) ⟶
    coinducedCoefficients (Rep.res f M) :=
  Rep.ofHom ⟨LinearMap.funLeft k M f, fun g => by
    ext v h
    change v (f h * f g) = v (f (h * g))
    rw [map_mul]⟩

/-- Function restriction commutes with the orbit embeddings. -/
theorem coinducedRestriction_inclusion :
    (Rep.resFunctor f).map (coinducedInclusion M) ≫ coinducedRestriction M f =
      coinducedInclusion (Rep.res f M) := by
  ext v
  rfl

/-- Restrict functions modulo orbit functions. -/
def shiftedRestriction : Rep.res f (shiftedCoefficients M) ⟶
    shiftedCoefficients (Rep.res f M) :=
  Rep.ofHom ⟨Submodule.mapQ _ _ (coinducedRestriction M f).hom.toLinearMap (by
    rintro _ ⟨m, rfl⟩
    exact ⟨m, rfl⟩), fun g => by
      apply LinearMap.ext
      intro x
      obtain ⟨v, rfl⟩ := (Submodule.mkQ_surjective
        (LinearMap.range (coinducedInclusion M).hom.toLinearMap)) x
      change (shiftedProjection (Rep.res f M)).hom
        ((coinducedRestriction M f).hom ((Rep.res f (coinducedCoefficients M)).ρ g v)) =
        (shiftedProjection (Rep.res f M)).hom
          ((coinducedCoefficients (Rep.res f M)).ρ g ((coinducedRestriction M f).hom v))
      exact congrArg (shiftedProjection (Rep.res f M)).hom
        (Rep.hom_comm_apply (coinducedRestriction M f) g v)⟩

/-- Quotient projection commutes with function restriction. -/
theorem shiftedRestriction_projection :
    (Rep.resFunctor f).map (shiftedProjection M) ≫ shiftedRestriction M f =
      coinducedRestriction M f ≫ shiftedProjection (Rep.res f M) := by
  ext v
  rfl

/-- A concrete comparison of the restricted and subgroup coefficient sequences. -/
def coinducedRestrictionSequence :
    (coinducedCoefficientSequence M).map (Rep.resFunctor f) ⟶
      coinducedCoefficientSequence (Rep.res f M) where
  τ₁ := 𝟙 _
  τ₂ := coinducedRestriction M f
  τ₃ := shiftedRestriction M f
  comm₁₂ := by
    change 𝟙 _ ≫ coinducedInclusion (Rep.res f M) = _
    rw [Category.id_comp]
    exact (coinducedRestriction_inclusion M f).symm
  comm₂₃ := (shiftedRestriction_projection M f).symm

variable [Fintype H]

/-- The quotient comparison intertwines the actual subgroup dimension shifts. -/
theorem shiftedRestriction_boundary (n : ℤ) :
    TateCohomology.δ (coinducedInjectiveSequence_shortExact M f) n =
      (tateCohomologyFunctor n).map (shiftedRestriction M f) ≫
        TateCohomology.δ (coinducedCoefficientSequence_shortExact (Rep.res f M)) n := by
  have h := TateCohomology.δ_naturality (coinducedInjectiveSequence_shortExact M f)
    (coinducedCoefficientSequence_shortExact (Rep.res f M))
    (coinducedRestrictionSequence M f) n
  have hi := (tateCohomologyFunctor (R := k) (G := H) (n + 1)).map_id
    (((coinducedCoefficientSequence M).map (Rep.resFunctor f)).X₁)
  dsimp only [coinducedRestrictionSequence] at h
  rw [hi, Category.comp_id] at h
  exact h

/-- Restricting quotient coefficients induces an isomorphism in every Tate degree. -/
theorem shiftedRestriction_isIso (hf : Function.Injective f) (n : ℤ) :
    IsIso ((tateCohomologyFunctor n).map (shiftedRestriction M f)) := by
  have := coinducedInjective_boundary_isIso M f hf n
  have := coinducedTate_boundary_isIso (Rep.res f M) n
  have h := shiftedRestriction_boundary M f n
  have : IsIso ((tateCohomologyFunctor n).map (shiftedRestriction M f) ≫
      TateCohomology.δ (coinducedCoefficientSequence_shortExact (Rep.res f M)) n) :=
    h ▸ inferInstance
  exact IsIso.of_isIso_comp_right _
    (TateCohomology.δ (coinducedCoefficientSequence_shortExact (Rep.res f M)) n)

end LocalClassFieldTheory
