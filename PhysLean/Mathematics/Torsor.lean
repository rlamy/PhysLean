/-
Copyright (c) 2025 Ronan Lamy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ronan Lamy
-/
import Mathlib.Algebra.Group.Action.Defs
/-!
# Torsors

This file defines multiplicative torsors.

-/

/-- A `Torsor G P` gives a structure to the type `P`,
acted on by an `Group G` with a multiplicative action given
by the `•` operation and a corresponding division given by the
`/` operation. In the case of a vector space, it is an affine
space. -/
class Torsor (G : outParam Type*) (P : Type*) [Group G] extends MulAction G P, HDiv P P G where
  /-- Torsor division and multiplication with the same element cancels out. -/
  div_smul : ∀ p₁ p₂ : P, (p₁ / p₂) • p₂ = p₁
  /-- Torsor multiplication and division with the same element cancels out. -/
  smul_div : ∀ (g : G) (p : P), (g • p) / p = g

namespace Torsor
attribute [simp] div_smul
attribute [simp] smul_div

variable [Group G] [Torsor G P]

lemma smul_right_cancel (p : P) (g1 g2 : G)
    (h : g1 • p = g2 • p) : g1 = g2 := by
  rw [← smul_div g1 p, h, smul_div]

@[simp]
lemma smul_right_cancel_iff (p : P) (g1 g2 : G) :
    g1 • p = g2 • p ↔ g1 = g2 :=
  ⟨smul_right_cancel p g1 g2, fun h ↦ h ▸ rfl⟩

@[simp]
lemma smul_div_assoc (g : G) (p1 p2 : P) :
    (g • p1) / p2 = g * (p1 / p2) := by
  apply smul_right_cancel p2
  rw [div_smul, mul_smul, div_smul]

@[simp]
lemma div_self (p : P) : p / p = (1 : G) := by
  rw [← one_mul (p / p), ← smul_div_assoc, smul_div]

@[simp]
lemma div_mul_div_cancel (p1 p2 p3: P) :
    (p1 / p2) * (p2 / p3) = p1 / p3 := by
  apply smul_right_cancel p3
  rw [mul_smul, div_smul, div_smul, div_smul]

@[simp]
lemma div_mul_div_cancel_outer [CommGroup G'] [Torsor G' P] (p1 p2 p3: P):
    (p2 / p1) * (p3 / p2) = p3 / p1 := by
  rw [mul_comm]
  simp

@[simp]
lemma inv_div_eq_div_rev (p1 p2: P) :
    (p1 / p2)⁻¹ = (p2 / p1) := by
  rw [inv_eq_of_mul_eq_one_left]
  simp

@[simp]
lemma div_smul_eq_div_mul_inv (p1 p2: P) (g : G) :
    p1 / g • p2 = p1 / p2 * g⁻¹ := by
  apply smul_right_cancel (g • p2)
  conv_rhs => rw [← mul_smul]
  simp
