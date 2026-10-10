/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXTerminalConicParameters
public import FLT.Mazur.PrincipalOpenNormalization

/-!
# The equality-depth terminal conic boundary at every preceding depth

The original incidence localization embeds openly into the complete Laurent
chart. The construction includes scale one and retains every conic function.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
  (h6 : W.a₆ = (π ^ (k + 1)) ^ 2 * b6) (hp : 2 * (k + 1) = n)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "c" => residue R b6
local notation "tx" => WeierstrassDilatation.tensorX W (π ^ (k + 1)) b3 b4 b6 K
local notation "e" => WeierstrassDilatation.residueLaurentEquiv D (k + 1)
  (Nat.zero_lt_succ k) hk b3 b4 b6 h3 h4 h6 hp
local notation "Q" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso (AlgEquiv.toRingEquiv
    (residueDividedConicOpenEquiv D k hk b3 b4 b6 h3 h4))))
local notation "E" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso (AlgEquiv.toRingEquiv e)))
local notation "b" => Spec.map (CommRingCat.ofHom
  (algebraMap (K[T;T⁻¹]) (Localization.Away ((e) tx))))
local notation "ψ" => residueLaurentConicMap D k hk b3 b4 b6 h3 h4 h6 hp
local notation "s" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
/-- The original oriented map is the full normalized principal inclusion at every depth. -/
theorem residueLaurentConicMap_spec_boundary :
    s = ((Q) ≪≫ (PrincipalOpenNormalization.specIso e tx).symm).hom ≫ b := by
  apply (cancel_mono (E).hom).mp
  rw [Category.assoc, ← PrincipalOpenNormalization.specIso_inclusion]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact congrArg (fun z => residueDividedConicMap D k hk b3 b4 b6 h3 h4 z)
    ((e).symm_apply_apply z)

/-- The oriented conic boundary is an open subscheme of the terminal Laurent chart. -/
instance residueLaurentConicMap_isOpenImmersion : IsOpenImmersion s := by
  rw [residueLaurentConicMap_spec_boundary]
  infer_instance

end FLT.Mazur.WeierstrassSuccessiveX
