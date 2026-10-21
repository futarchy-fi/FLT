/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationScalarComparisonPullback
public import FLT.Mazur.SchemePullbackThroughOpen

/-!
# Full comparison geometry from original kernel-pair neighborhoods

Both original endpoints survive the kernel-pair identification. If its
original projection factors through an open, the whole branch comparison
is the pullback of the comparison restricted to that original open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeRelationScalarBaseChange
set_option backward.isDefEq.respectTransparency false
variable {R S : Type} [CommRing R] [CommRing S] {D X : Scheme.{0}}
  (a b : D ⟶ X) (f : X ⟶ Spec (.of R)) (h : a ≫ f = b ≫ f)
  (ρ : R →+* S)
local notation "g" => Spec.map (CommRingCat.ofHom ρ)
local notation "c" => SchemeScalarImageQuotient.projection (pullback.snd f g)
local notation "u" => pullback.fst f f
local notation "v" => pullback.snd f f

/-- The original kernel-pair map retains its first full source coordinate. -/
@[reassoc] theorem kernelOriginal_first :
    kernelOriginal f ρ ≫ u = pullback.fst c c ≫ pullback.fst f g := by
  let _ := kernelComparison_isIso_of_original u v f pullback.condition ρ
    (IsPullback.of_hasPullback f f)
  apply (cancel_epi (kernelComparison u v f pullback.condition ρ)).mp
  rw [kernelComparison_kernelOriginal_assoc, kernelComparison_first_assoc, first_original]

/-- The original kernel-pair map also retains the independent second coordinate. -/
@[reassoc] theorem kernelOriginal_second :
    kernelOriginal f ρ ≫ v = pullback.snd c c ≫ pullback.fst f g := by
  let _ := kernelComparison_isIso_of_original u v f pullback.condition ρ
    (IsPullback.of_hasPullback f f)
  apply (cancel_epi (kernelComparison u v f pullback.condition ρ)).mp
  rw [kernelComparison_kernelOriginal_assoc, kernelComparison_second_assoc, second_original]

variable (U : (pullback f f).Opens)
  (j : pullback
    (SchemeScalarImageQuotient.projection (pullback.snd f (Spec.map (CommRingCat.ofHom ρ))))
    (SchemeScalarImageQuotient.projection (pullback.snd f (Spec.map (CommRingCat.ofHom ρ)))) ⟶
      U.toScheme)
  (hj : j ≫ U.ι = kernelOriginal f ρ)

/-- The full relation maps to the original comparison's neighborhood preimage. -/
def comparisonNeighborhoodSource : relation a f ρ ⟶
    ((pullback.lift a b h) ⁻¹ᵁ U).toScheme :=
  SchemePullbackThroughOpen.sourceMap (kernelComparison_isPullback a b f h ρ) U j hj

/-- Restricting the original comparison still gives the whole branch comparison by pullback. -/
theorem comparisonNeighborhood_isPullback :
    IsPullback (comparisonNeighborhoodSource a b f h ρ U j hj)
      (kernelComparison a b f h ρ) ((pullback.lift a b h) ∣_ U) j :=
  SchemePullbackThroughOpen.isPullback (kernelComparison_isPullback a b f h ρ) U j hj

include hj in
/-- Any base-change stable local comparison geometry holds on the entire branch comparison. -/
theorem kernelComparison_property_of_neighborhood (P : MorphismProperty Scheme.{0})
    [P.IsStableUnderBaseChange] (hP : P ((pullback.lift a b h) ∣_ U)) :
    P (kernelComparison a b f h ρ) :=
  MorphismProperty.of_isPullback (comparisonNeighborhood_isPullback a b f h ρ U j hj) hP

end FLT.Mazur.SchemeRelationScalarBaseChange
