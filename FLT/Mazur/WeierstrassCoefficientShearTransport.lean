/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearGluing
public import FLT.Mazur.CartesianCoefficientTransportNaturality
public import FLT.Mazur.SchemeChartOverlapComparison

/-!
# Whole-model coefficient transport on the complete sheared equation gluing

The constructed cartesian square supplies whole-model overlap transport, its
composition law, and compatibility with the original coefficient pullback.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "s" => coefficientShearGluedStructure hπ data S r j hj
local notation "p" => coefficientShearGluedProjection hπ data S r j hj
local notation "H" => IsPullback.flip (coefficientShearGlued_isPullback hπ data S r j hj)
variable {T : Scheme.{u}} (a b : T ⟶ Spec (.of S))
  (h : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) =
    b ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- Transport on the entire glued equation model over any coefficient overlap. -/
def coefficientShearTransport : pullback a s ≅ pullback b s :=
  CartesianCoefficientTransport.iso H a b h

/-- The transport retains the actual overlap coefficient projection. -/
@[reassoc] theorem coefficientShearTransport_structure :
    (coefficientShearTransport hπ data S r j hj a b h).hom ≫ pullback.fst b s =
      pullback.fst a s :=
  CartesianCoefficientTransport.map_coefficient H a b h

/-- The entire original finite-model projection is unchanged by overlap transport. -/
@[reassoc] theorem coefficientShearTransport_projection :
    (coefficientShearTransport hπ data S r j hj a b h).hom ≫ pullback.snd b s ≫ p =
      pullback.snd a s ≫ p :=
  CartesianCoefficientTransport.map_original H a b h

/-- The whole equation gluing satisfies the overlap cocycle on every triple coefficient lift. -/
@[reassoc] theorem coefficientShearTransport_comp (c : T ⟶ Spec (.of S))
    (hb : b ≫ q = c ≫ q) :
    (coefficientShearTransport hπ data S r j hj a b h).hom ≫
        (coefficientShearTransport hπ data S r j hj b c hb).hom =
      (coefficientShearTransport hπ data S r j hj a c (h.trans hb)).hom :=
  CartesianCoefficientTransport.map_comp H a b h c hb

/-- Repeated coefficient lifts act by the identity on the whole model. -/
theorem coefficientShearTransport_self :
    (coefficientShearTransport hπ data S r j hj a a rfl).hom = 𝟙 _ :=
  CartesianCoefficientTransport.map_self H a

local notation "base" => finiteGlobalStructure hπ data j hj
local notation "s₀" => pullback.fst q base
local notation "H₀" => IsPullback.flip (IsPullback.of_hasPullback q base)
local notation "e" => coefficientShearGluedIso hπ data S r j hj

/-- Reconstruction is an isomorphism on every entire coefficient overlap. -/
def coefficientShearOverlapReconstructionIso : pullback a s ≅ pullback a s₀ :=
  SchemeChartOverlapComparison.overlapIso a s a s₀ (Iso.refl _) e
    (Category.id_comp a) rfl

/-- Reconstruction on each coefficient overlap keeps the complete original model. -/
def coefficientShearOverlapReconstruction :=
  (coefficientShearOverlapReconstructionIso hπ data S r j hj a).hom

/-- The reconstruction is exactly the morphism induced by the original full-model comparison. -/
theorem coefficientShearOverlapReconstruction_eq :
    coefficientShearOverlapReconstruction hπ data S r j hj a =
      CartesianCoefficientTransport.objectMap a (e).hom rfl := by
  apply pullback.hom_ext
  · change (coefficientShearOverlapReconstructionIso hπ data S r j hj a).hom ≫ _ = _
    rw [coefficientShearOverlapReconstructionIso,
      SchemeChartOverlapComparison.overlapIso_fst,
      CartesianCoefficientTransport.objectMap_coefficient, Iso.refl_hom, Category.comp_id]
    rfl
  · change (coefficientShearOverlapReconstructionIso hπ data S r j hj a).hom ≫ _ = _
    rw [coefficientShearOverlapReconstructionIso,
      SchemeChartOverlapComparison.overlapIso_snd,
      CartesianCoefficientTransport.objectMap_object]
    rfl

/-- Equation transport is the original cartesian transport under the actual reconstruction. -/
@[reassoc] theorem coefficientShearTransport_reconstruction :
    (coefficientShearTransport hπ data S r j hj a b h).hom ≫
        coefficientShearOverlapReconstruction hπ data S r j hj b =
      coefficientShearOverlapReconstruction hπ data S r j hj a ≫
        (CartesianCoefficientTransport.iso H₀ a b h).hom := by
  rw [coefficientShearOverlapReconstruction_eq, coefficientShearOverlapReconstruction_eq]
  exact CartesianCoefficientTransport.map_naturality H a b h H₀ (e).hom (𝟙 _)
    (by exact (Category.comp_id p).symm) rfl

end FLT.Mazur.WeierstrassDividedDepth
