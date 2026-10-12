/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLinePullback
public import FLT.Mazur.SectionCartesianKernel
public import FLT.Mazur.StructureCohomologyOverIso

/-!
# Cohomology of point divisors under actual curve isomorphisms

The comparison pulls back the full point ideal and its positive divisor line.
It is linear over the original field, so it preserves both vanishing and ranks.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type} [Field k] {X Y : Scheme}

/-- Geometric pullback along an isomorphism preserves actual scalar cohomology. -/
def moduleScalarHPullbackIsoEquiv (e : X ≅ Y) (f : Y ⟶ Spec (.of k))
    (M : Y.Modules) (n : ℕ) :
    ModuleScalarH f M n ≃ₗ[k]
      ModuleScalarH (e.hom ≫ f) ((Scheme.Modules.pullback e.hom).obj M) n :=
  (moduleScalarHRestrictIsoEquiv e f M n).trans
    (((moduleScalarHFunctor (e.hom ≫ f) n).mapIso
      ((restrictFunctorIsoPullback e.hom).app M)).toLinearEquiv)

/-- An isomorphism sending one section to another pulls back their entire ideals. -/
theorem pointIdeal_comap_of_overIso (e : X ≅ Y)
    (f : Y ⟶ Spec (.of k)) (g : X ⟶ Spec (.of k)) [IsSeparated f]
    (he : e.hom ≫ f = g) (s : Spec (.of k) ⟶ X) (t : Spec (.of k) ⟶ Y)
    (hs : s ≫ g = 𝟙 _) (ht : t ≫ f = 𝟙 _) (hst : s ≫ e.hom = t) :
    t.ker.comap e.hom = s.ker := by
  have H : IsPullback e.hom g f (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simpa using he⟩
  exact section_ker_comap_of_cartesian H s t hs ht (by simpa using hst)

/-- The positive point lines have the same field-linear cohomology under the given map. -/
def pointDivisorScalarHIsoEquiv (e : X ≅ Y)
    (f : Y ⟶ Spec (.of k)) (g : X ⟶ Spec (.of k)) [IsSeparated f]
    (he : e.hom ≫ f = g) (s : Spec (.of k) ⟶ X) (t : Spec (.of k) ⟶ Y)
    (hs : s ≫ g = 𝟙 _) (ht : t ≫ f = 𝟙 _) (hst : s ≫ e.hom = t)
    (hI : EffectiveCartier s.ker) (hJ : EffectiveCartier t.ker) (n : ℕ) :
    ModuleScalarH f (divisorLineBundle t.ker hJ) n ≃ₗ[k]
      ModuleScalarH g (divisorLineBundle s.ker hI) n := by
  let l := divisorLinePullbackIsoOfEq e.hom hJ hI
    (pointIdeal_comap_of_overIso e f g he s t hs ht hst)
  have a := (moduleScalarHPullbackIsoEquiv e f (divisorLineBundle t.ker hJ) n).trans
    (((moduleScalarHFunctor (e.hom ≫ f) n).mapIso l).toLinearEquiv)
  exact he ▸ a

end FLT.Mazur.FCurve
