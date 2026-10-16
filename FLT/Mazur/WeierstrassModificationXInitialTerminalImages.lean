/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInitialTerminalComparison
public import FLT.Mazur.WeierstrassModificationXInitialTerminalUnits
public import FLT.Mazur.WeierstrassDilatationTerminalHorizontalLocus
public import FLT.Mazur.PrincipalOpenTensorRange

/-!
# Exact standard terminal images of the two original initial boundaries

Each full initial Laurent boundary has exactly its selected terminal
puncture as image. Coverage uses the original entire tensor overlap.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "U" => W.map q
local notation "J" => ideal Q (parameter R π m)
local notation "hJ" => arithmeticParameterIdeal_nilpotent π m
local notation "r" => WeierstrassDilatation.terminalTangentRoot U (q s) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
local notation "hrI" => WeierstrassDilatation.terminalTangentRoot_mem U (q s) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
local notation "hr" => WeierstrassDilatation.terminalTangentRoot_equation U (q s) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
local notation "h4₀" => arithmeticCoefficient_mem π m h4
local notation "h6₀" => arithmeticCoefficient_mem π m h6
local notation "c" => WeierstrassDilatation.arithmeticTerminalSmoothing π m W s
  b3 b4 b6 ha hs h2 h4 h6
local notation "e" => WeierstrassDilatation.arithmeticTerminalNodeIso π m W s
  b3 b4 b6 ha hs h2 h4 h6

local notation "E" => initialTerminalArithmeticNodeEvaluation
  π m W s b3 b4 b6 ha hs h2 h3 h4 h6
local notation "P" => arithmeticInitialPunctureIso π m W s b3 b4 b6 ha hs h2 h3 h4 h6
local notation "u" label => arithmeticInitialPunctureToTensorBoundary
  π m W s b3 b4 b6 ha h2 h3 h4 h6 label hs
local notation "t₀" => t W s b3 b4 b6
local notation "x" => WeierstrassDilatation.x W s b3 b4 b6
local notation "a" => overlapEquiv W s b3 b4 b6
local notation "i" => PrincipalOpenTensor.inclusion Q t₀
local notation "B" => Iso.hom (PrincipalOpenTensor.transitionIso Q x t₀ a) ≫
  PrincipalOpenTensor.inclusion Q x

attribute [local irreducible] arithmeticInitialPunctureIso
  arithmeticInitialPunctureToTensorBoundary initialTerminalArithmeticNodeEvaluation

include h3 in
/-- Either standard terminal puncture lies in the full original horizontal open. -/
theorem initialTerminalArithmeticPuncture_horizontal (opposite : Bool)
    (z : Spec (.of (NodalFiber.Coordinate c)))
    (hz : (if opposite then NodalFiber.p c else NodalFiber.q c) ∉ z.asIdeal) :
    ∃ y, PrincipalOpenTensor.inclusion Q x y = (e).hom z := by
  apply (PrincipalOpenTensor.mem_inclusion_range Q x ((e).hom z)).mpr
  change WeierstrassDilatation.tensorTerminalNodeEquiv W s
    b3 b4 b6 Q r J hJ hrI (ha.map q) h4₀ h6₀ hr ((1 : Q) ⊗ₜ[R] x) ∉ z.asIdeal
  rw [WeierstrassDilatation.tensorTerminalNodeEquiv_tmul, one_smul,
    WeierstrassDilatation.coefficientMap_x]
  exact WeierstrassDilatation.terminalNodePuncture_horizontal U (q s)
    (q b3) (q b4) (q b6) r J hJ hrI (ha.map q)
    (arithmeticCoefficient_mem π m h3) h4₀ h6₀ hr z.asIdeal opposite hz

/-- Both initial Laurent boundaries jointly cover the entire original terminal horizontal open. -/
theorem initialTerminalArithmeticNodeEvaluation_cover
    (z : Spec (.of (NodalFiber.Coordinate c)))
    (hz : ∃ y, PrincipalOpenTensor.inclusion Q x y = (e).hom z) :
    ∃ label : Bool, ∃ y, Spec.map (CommRingCat.ofHom (E label).toRingHom) y = z := by
  obtain ⟨y, hy⟩ := hz
  let w := (PrincipalOpenTensor.transitionIso Q x t₀ a).inv y
  obtain ⟨label, v, hv⟩ : ∃ label : Bool, ∃ v, (u label) v = w := by
    obtain h | h := arithmeticInitialPunctures_tensor_cover
      π m W s b3 b4 b6 ha h2 h3 h4 h6 hs w
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  refine ⟨label, (P).inv v, ?_⟩
  rw [← arithmeticInitialPunctureIso_terminal_boundary
    π m W s b3 b4 b6 ha hs h2 h3 h4 h6]
  change (e).inv (PrincipalOpenTensor.inclusion Q x
    ((PrincipalOpenTensor.transitionIso Q x t₀ a).hom
      ((u label) ((P).hom ((P).inv v))))) = z
  rw [← Scheme.Hom.comp_apply (P).inv (P).hom, Iso.inv_hom_id]
  change (e).inv (PrincipalOpenTensor.inclusion Q x
    ((PrincipalOpenTensor.transitionIso Q x t₀ a).hom ((u label) v))) = z
  rw [hv]
  change (e).inv (PrincipalOpenTensor.inclusion Q x
    ((PrincipalOpenTensor.transitionIso Q x t₀ a).hom
      ((PrincipalOpenTensor.transitionIso Q x t₀ a).inv y))) = z
  rw [← Scheme.Hom.comp_apply (PrincipalOpenTensor.transitionIso Q x t₀ a).inv
    (PrincipalOpenTensor.transitionIso Q x t₀ a).hom, Iso.inv_hom_id]
  change (e).inv (PrincipalOpenTensor.inclusion Q x y) = z
  rw [hy, ← Scheme.Hom.comp_apply (e).hom (e).inv, Iso.hom_inv_id]
  rfl

/-- Each original initial label has precisely its full standard terminal puncture as image. -/
theorem initialTerminalArithmeticNodeEvaluation_range (opposite : Bool) :
    Set.range (Spec.map (CommRingCat.ofHom (E opposite).toRingHom)) =
      (PrimeSpectrum.basicOpen (if opposite then NodalFiber.p c else NodalFiber.q c) :
        Set (PrimeSpectrum (NodalFiber.Coordinate c))) := by
  ext z
  change (∃ y, Spec.map (CommRingCat.ofHom (E opposite).toRingHom) y = z) ↔ _
  constructor
  · rintro ⟨y, rfl⟩
    exact y.asIdeal.notMem_of_isUnit
      (initialTerminalArithmeticSelected_unit π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite)
  · intro hz
    obtain ⟨label, y, hy⟩ := initialTerminalArithmeticNodeEvaluation_cover
      π m W s b3 b4 b6 ha hs h2 h3 h4 h6 z
        (initialTerminalArithmeticPuncture_horizontal
          π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite z hz)
    have hl : label = opposite := by
      by_contra hne
      have he : (if opposite then NodalFiber.p c else NodalFiber.q c) =
          (if label then NodalFiber.q c else NodalFiber.p c) := by
        cases label <;> cases opposite
        · exact False.elim (hne rfl)
        · rfl
        · rfl
        · exact False.elim (hne rfl)
      have hn := initialTerminalArithmeticUnselected_nilpotent
        π m W s b3 b4 b6 ha hs h2 h3 h4 h6 label
      change (if opposite then NodalFiber.p c else NodalFiber.q c) ∉ z.asIdeal at hz
      apply hz
      rw [← hy, he]
      exact nilpotent_iff_mem_prime.mp hn y.asIdeal inferInstance
    exact ⟨y, hl ▸ hy⟩

end FLT.Mazur.WeierstrassModificationX
