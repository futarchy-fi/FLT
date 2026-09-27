/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.TorsionPairingNondegenerate
public import FLT.EllipticCurve.WeilPairing
/-!
# A bilinear candidate on the geometric-torsion interface

The translation-ratio construction transports to the existing n-torsion
module. It can be passed directly to `TorsionWeilPairing.ofBilinear` once
Galois equivariance has been established.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine
namespace WeierstrassCurve
variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F)
/-- The module and additive-subgroup presentations of n-torsion are equivalent. -/
def nTorsionEquivTorsionKernel (n : ℕ) :
    E.nTorsion n ≃+ Affine.Point.torsionKernel (E⁄F) n where
  toFun P := ⟨P.val, by
    change n • P.val = 0
    simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using P.property⟩
  invFun P := ⟨P.val, by
    simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using
      (show n • P.val = 0 from P.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The geometric construction as a bilinear map on the existing n-torsion module. -/
noncomputable def torsionPairingCandidate [IsAlgClosed F] [E.IsElliptic]
    {n : ℕ} (hn : n ≠ 0) (hchar : (n : F) ≠ 0) :
    E.nTorsion n →+ E.nTorsion n →+ Additive (rootsOfUnity n F) := by
  letI : (E⁄F).IsElliptic :=
    inferInstanceAs (E.map (algebraMap F F)).IsElliptic
  let e := E.nTorsionEquivTorsionKernel n
  let b := Affine.FunctionField.torsionPairingBilinear (E⁄F) hn hchar
  exact AddMonoidHom.mk' (fun P => (b (e P)).comp e.toAddMonoidHom)
    (fun P Q => by ext R; simp)
/-- The geometric pairing candidate is alternating. -/
theorem torsionPairingCandidate_self [IsAlgClosed F] [E.IsElliptic]
    {n : ℕ} (hn : n ≠ 0) (hchar : (n : F) ≠ 0) (P : E.nTorsion n) :
    E.torsionPairingCandidate hn hchar P P = 0 := by
  let : (E⁄F).IsElliptic :=
    inferInstanceAs (E.map (algebraMap F F)).IsElliptic
  exact Affine.FunctionField.torsionPairing_self (E⁄F) hn hchar
    (E.nTorsionEquivTorsionKernel n P)
/-- The geometric pairing candidate is nondegenerate in its first argument. -/
theorem torsionPairingCandidate_nondegenerate [IsAlgClosed F] [E.IsElliptic]
    {n : ℕ} (hn : n ≠ 0) (hchar : (n : F) ≠ 0) (P : E.nTorsion n)
    (hP : ∀ Q, E.torsionPairingCandidate hn hchar P Q = 0) : P = 0 := by
  let : (E⁄F).IsElliptic :=
    inferInstanceAs (E.map (algebraMap F F)).IsElliptic
  apply (E.nTorsionEquivTorsionKernel n).injective
  rw [map_zero]
  apply Affine.FunctionField.torsionPairing_left_nondegenerate (E⁄F) hn hchar
  intro Q
  exact hP ((E.nTorsionEquivTorsionKernel n).symm Q)
end WeierstrassCurve
