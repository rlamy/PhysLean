/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7

The following was proved by Aristotle:

- @[sorryful]
lemma solidSphere_inertiaTensor (m R : ℝ≥0) (hr : R ≠ 0) :
    (solidSphere 3 m R).inertiaTensor = (2/5 * m.1 * R.1^2) • (1 : Matrix _ _ _)
-/

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.ClassicalMechanics.RigidBody.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls


/-!

# The solid sphere as a rigid body

In this module we consider the solid sphere as a rigid body, and compute its mass,
center of mass and inertia tensor.

-/

open Manifold

open MeasureTheory

namespace RigidBody

open NNReal

/-- The solid sphere as a rigid body. -/
noncomputable def solidSphere (d : ℕ) (m R : ℝ≥0) : RigidBody d where
  ρ := ⟨⟨fun f => m / volume.real (Metric.closedBall (0 : Space d) R) *
      ∫ x in Metric.closedBall (0 : Space d) R, f x ∂volume,
    by
    intro f g
    simp only [ContMDiffMap.coe_add, Pi.add_apply]
    rw [integral_add]
    ring
    · exact IntegrableOn.integrable
        (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 R) (by fun_prop))
    · exact IntegrableOn.integrable
        (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 R) (by fun_prop))⟩, by
      intro r f
      simp only [ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [integral_const_mul]
      ring⟩

lemma solidSphere_mass {d : ℕ} (m R : ℝ≥0) (hr : R ≠ 0) : (solidSphere d.succ m R).mass = m := by
  simp only [mass, solidSphere]
  simp only [Nat.succ_eq_add_one, LinearMap.coe_mk, AddHom.coe_mk, ContMDiffMap.coeFn_mk,
    integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter, smul_eq_mul,
    mul_one]
  have h1 : (@volume (Space d.succ) measureSpaceOfInnerProductSpace).real
      (Metric.closedBall 0 R) ≠ 0 := by
    refine (measureReal_ne_zero_iff ?_).mpr ?_
    · rw [EuclideanSpace.volume_closedBall]
      simp
      exact not_eq_of_beq_eq_false rfl
    · rw [EuclideanSpace.volume_closedBall]
      simp only [ENNReal.ofReal_coe_nnreal, Nat.succ_eq_add_one, Fintype.card_fin, Nat.cast_add,
        Nat.cast_one, ne_eq, mul_eq_zero, Nat.add_eq_zero, one_ne_zero, and_false,
        not_false_eq_true, pow_eq_zero_iff, ENNReal.coe_eq_zero, ENNReal.ofReal_eq_zero, not_or,
        not_le]
      apply And.intro
      · exact hr
      · positivity
  field_simp

/-- The center of mass of a solid sphere located at the origin is `0`. -/
lemma solidSphere_centerOfMass {d : ℕ} (m R : ℝ≥0) : (solidSphere d.succ m R).centerOfMass = 0 := by
  ext i
  simp only [centerOfMass, solidSphere, one_div, LinearMap.coe_mk, AddHom.coe_mk,
    ContMDiffMap.coeFn_mk, smul_eq_mul, PiLp.zero_apply, mul_eq_zero, inv_eq_zero, div_eq_zero_iff,
    coe_eq_zero]
  right
  right
  suffices ∫ x in Metric.closedBall (0 : Space d.succ) R, x i ∂MeasureSpace.volume
    = -∫ x in Metric.closedBall (0 : Space d.succ) R, x i ∂MeasureSpace.volume by linarith
  rw [← integral_neg]
  simp only [← integral_indicator measurableSet_closedBall, Set.indicator, Metric.mem_closedBall,
    dist_zero_right]
  rw [← integral_neg_eq_self]
  norm_num

/-- The moment of inertia tensor of a solid sphere through its center of mass is
  `2/5 m R^2 * I`. -/
noncomputable section AristotleLemmas

lemma integral_closedBall_coord_mul_coord_eq_zero {d : ℕ} (R : ℝ) (i j : Fin d) (h : i ≠ j) :
    ∫ x in Metric.closedBall (0 : Space d) R, x i * x j = 0 := by
      -- Define the reflection map σ that swaps x_i and x_j.
      set σ : Space d → Space d := fun x => fun k => if k = i then -x i else x k;
      -- Since σ is a reflection, it is an isometry, so the measure is preserved.
      have h_iso : MeasureTheory.MeasurePreserving σ (MeasureTheory.MeasureSpace.volume) (MeasureTheory.MeasureSpace.volume) := by
        -- Since σ is a linear transformation with determinant -1, it is measure-preserving.
        have h_linear : ∃ L : Space d →ₗ[ℝ] Space d, σ = L := by
          refine' ⟨ _, _ ⟩;
          refine' { toFun := σ, map_add' := _, map_smul' := _ };
          all_goals norm_num +zetaDelta at *;
          · exact fun x y => by ext k; by_cases hk : k = i <;> simp +decide [ hk ] ; ring;
          · exact fun m x => by ext k; aesop;
        aesop;
        have h_det : LinearMap.det w = -1 := by
          have h_det : w = Matrix.toLin' (Matrix.diagonal (fun k => if k = i then -1 else 1)) := by
            ext x k;
            simp +decide [ ← h_1, Matrix.mulVec_diagonal ];
            erw [ Matrix.toLin'_apply ] ; aesop;
            · simp +decide [ Matrix.mulVec, dotProduct ];
              simp +decide [ Matrix.diagonal, Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ];
            · rw [ Matrix.mulVec_diagonal ] ; aesop;
          aesop;
          erw [ LinearMap.det_toLin' ] ; norm_num [ Matrix.det_diagonal ];
        refine' ⟨ _, _ ⟩;
        · fun_prop;
        · ext s hs;
          rw [ MeasureTheory.Measure.map_apply ];
          · erw [ MeasureTheory.Measure.addHaar_preimage_linearMap ] ; aesop;
            linarith;
          · exact w.continuous_of_finiteDimensional.measurable;
          · exact hs;
      -- Since σ is an isometry, we can change variables in the integral.
      have h_change : ∫ x in Metric.closedBall (0 : Space d) R, x i * x j = ∫ x in Metric.closedBall (0 : Space d) R, (-x i) * x j := by
        rw [ ← MeasureTheory.integral_indicator ( measurableSet_closedBall ), ← MeasureTheory.integral_indicator ( measurableSet_closedBall ) ];
        rw [ ← h_iso.integral_comp ];
        · simp [σ];
          congr with x ; by_cases hi : x i = 0 <;> by_cases hj : x j = 0 <;> simp +decide [ *, Set.indicator ];
          · aesop;
          · simp +decide [ h.symm, norm ];
            simp +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne', h ];
        · -- The reflection map σ is continuous, hence measurable.
          have h_cont : Continuous σ := by
            rw [ continuous_pi_iff ];
            aesop;
            · fun_prop;
            · exact continuous_apply _;
          have h_inj : Function.Injective σ := by
            intro x y hxy; ext k; replace hxy := congr_fun hxy k; aesop;
          exact h_cont.measurable.measurableEmbedding h_inj;
      norm_num [ MeasureTheory.integral_neg ] at * ; linarith

open MeasureTheory Manifold RigidBody

lemma integral_closedBall_coord_sq_eq {d : ℕ} (R : ℝ) (i j : Fin d) :
    ∫ x in Metric.closedBall (0 : Space d) R, (x i)^2 = ∫ x in Metric.closedBall (0 : Space d) R, (x j)^2 := by
      have h_perm : ∃ σ : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
        σ (EuclideanSpace.single i 1) = EuclideanSpace.single j 1 ∧ σ (EuclideanSpace.single j 1) = EuclideanSpace.single i 1 ∧ ∀ k : Fin d, k ≠ i → k ≠ j → σ (EuclideanSpace.single k 1) = EuclideanSpace.single k 1 := by
          -- Define the permutation σ that swaps i and j.
          set σ : Equiv.Perm (Fin d) := Equiv.swap i j;
          refine' ⟨ _, _, _, _ ⟩;
          exact?;
          · ext k ; by_cases hk : k = j <;> aesop;
            rw [ Equiv.swap_apply_def ] at a ; aesop;
          · ext k ; aesop;
            rw [ Equiv.swap_apply_def ] at h ; aesop;
            tauto;
          · aesop;
            ext l; by_cases h : l = k <;> aesop;
            · rw [ Equiv.swap_apply_def ] ; aesop;
            · rw [ Equiv.swap_apply_def ] at * ; aesop;
      obtain ⟨ σ, hσ₁, hσ₂, hσ₃ ⟩ := h_perm;
      -- Since σ is an isometry, the measure is preserved, so the integrals over the closed ball are equal.
      have h_measure_preserving : ∀ (f : EuclideanSpace ℝ (Fin d) → ℝ), MeasureTheory.IntegrableOn f (Metric.closedBall 0 R) → ∫ x in Metric.closedBall 0 R, f x = ∫ x in Metric.closedBall 0 R, f (σ x) := by
        have h_measure_preserving : ∀ (f : EuclideanSpace ℝ (Fin d) → ℝ), MeasureTheory.IntegrableOn f (Metric.closedBall 0 R) → ∫ x in Metric.closedBall 0 R, f x = ∫ x in Metric.closedBall 0 R, f (σ x) := by
          intro f hf
          have h_measure_preserving : MeasureTheory.MeasurePreserving σ MeasureTheory.MeasureSpace.volume MeasureTheory.MeasureSpace.volume := by
            exact?
          rw [ ← MeasureTheory.integral_indicator ( measurableSet_closedBall ), ← MeasureTheory.integral_indicator ( measurableSet_closedBall ) ];
          rw [ ← h_measure_preserving.integral_comp ];
          · simp +decide [ Set.indicator ];
          · exact σ.toHomeomorph.measurableEmbedding;
        exact h_measure_preserving;
      convert h_measure_preserving ( fun x => x i ^ 2 ) _ using 3;
      · -- Since σ is a linear map, we can express x as a linear combination of the basis vectors.
        have h_linear : ∀ x : EuclideanSpace ℝ (Fin d), σ x = ∑ k, x k • σ (EuclideanSpace.single k 1) := by
          intro x;
          convert σ.pi_apply_eq_sum_univ x;
          aesop;
        rw [ h_linear ];
        rw [ Finset.sum_apply, Finset.sum_eq_single j ] <;> simp +contextual [ hσ₁, hσ₂, hσ₃ ];
        intro k hk; by_cases hi : k = i <;> simp +decide [ hi, hk, hσ₁, hσ₂, hσ₃ ] ;
        · grind;
        · tauto;
      · exact ContinuousOn.integrableOn_compact ( ProperSpace.isCompact_closedBall _ _ ) ( Continuous.continuousOn ( by exact Continuous.pow ( continuous_apply _ ) _ ) )

open MeasureTheory Manifold RigidBody

lemma volume_closedBall_three (R : ℝ) (hR : 0 ≤ R) :
    volume.real (Metric.closedBall (0 : Space 3) R) = (4/3) * Real.pi * R^3 := by
      rw [ MeasureTheory.measureReal_def ];
      norm_num +zetaDelta at *;
      rw [ ENNReal.toReal_ofReal, ENNReal.toReal_ofReal ] <;> linarith [ Real.pi_pos ]

open MeasureTheory Manifold RigidBody

lemma integral_closedBall_norm_sq_three (R : ℝ) (hR : 0 ≤ R) :
    ∫ x in Metric.closedBall (0 : Space 3) R, ‖x‖^2 = (4/5) * Real.pi * R^5 := by
      have := @MeasureTheory.integral_fun_norm_addHaar;
      specialize @this ( EuclideanSpace ℝ ( Fin 3 ) ) _ _ _ ℝ _ _ _;
      specialize this ( MeasureTheory.MeasureSpace.volume ) ( fun r => if r ≤ R then r ^ 2 else 0 ) ; norm_num at this;
      convert this using 1;
      · rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
        exact measurableSet_closedBall;
      · rw [ show ( MeasureTheory.MeasureSpace.volume.real ( Metric.ball ( 0 : EuclideanSpace ℝ ( Fin 3 ) ) 1 ) ) = ( 4 / 3 ) * Real.pi by
              norm_num [ MeasureTheory.measureReal_def ];
              rw [ ENNReal.toReal_ofReal ] <;> linarith [ Real.pi_pos ] ] ; ring;
        -- Let's simplify the integral.
        have h_integral : ∫ y in Set.Ioi (0 : ℝ), (if y ≤ R then y ^ 4 else 0) = ∫ y in Set.Ioc (0 : ℝ) R, y ^ 4 := by
          rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
          simpa only [ ← ite_and ];
        rw [ h_integral, ← intervalIntegral.integral_of_le ] <;> norm_num <;> linarith

open MeasureTheory Manifold RigidBody

lemma integral_closedBall_coord_sq_eq_div_three (R : ℝ) (i : Fin 3) :
    ∫ x in Metric.closedBall (0 : Space 3) R, (x i)^2 = (1/3) * ∫ x in Metric.closedBall (0 : Space 3) R, ‖x‖^2 := by
      -- The integral of ‖x‖^2 over the closed ball can be expressed as the sum of the integrals of x_i^2 over the closed ball.
      have h_sum : ∫ x in Metric.closedBall (0 : Space 3) R, ‖x‖ ^ 2 = ∑ i : Fin 3, ∫ x in Metric.closedBall (0 : Space 3) R, (x i) ^ 2 := by
        -- By definition of the norm, we know that ‖x‖^2 = ∑ i, x i^2.
        have h_norm_sq : ∀ x : Space 3, ‖x‖^2 = ∑ i : Fin 3, x i^2 := by
          -- By definition of the norm, we know that ‖x‖^2 = x · x.
          simp [EuclideanSpace.norm_eq];
          -- The square root function is the inverse of the square function for non-negative numbers.
          intro x
          apply Real.sq_sqrt
          apply Finset.sum_nonneg
          intro i _
          apply sq_nonneg;
        rw [ funext h_norm_sq, MeasureTheory.integral_finset_sum ];
        exact fun i _ => ContinuousOn.integrableOn_compact ( ProperSpace.isCompact_closedBall _ _ ) ( by exact Continuous.continuousOn ( by exact Continuous.pow ( continuous_apply i ) _ ) );
      have := integral_closedBall_coord_sq_eq R i 0; ( have := integral_closedBall_coord_sq_eq R i 1; ( have := integral_closedBall_coord_sq_eq R i 2; ( norm_num [ Fin.sum_univ_three ] at *; linarith!; ) ) )

end AristotleLemmas

@[sorryful]
lemma solidSphere_inertiaTensor (m R : ℝ≥0) (hr : R ≠ 0) :
    (solidSphere 3 m R).inertiaTensor = (2/5 * m.1 * R.1^2) • (1 : Matrix _ _ _) := by
  unfold RigidBody.inertiaTensor; aesop;
  ext i j; simp +decide [ RigidBody.solidSphere ] ; ring_nf; aesop;
  · -- Substitute the known integrals into the expression.
    have h_integrals : ∫ x in Metric.closedBall (0 : Space 3) R, ∑ j : Fin 3, x j ^ 2 = (4 / 5) * Real.pi * R ^ 5 ∧ ∫ x in Metric.closedBall (0 : Space 3) R, x i ^ 2 = (1 / 3) * (4 / 5) * Real.pi * R ^ 5 := by
      aesop;
      · convert integral_closedBall_norm_sq_three R ( by positivity ) using 1 ; norm_num [ EuclideanSpace.norm_eq ] ; ring;
        exact MeasureTheory.setIntegral_congr_fun measurableSet_closedBall fun x hx => by rw [ Real.sq_sqrt ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ] ;
      · have := integral_closedBall_coord_sq_eq_div_three ( R : ℝ ) i; norm_num [ integral_closedBall_norm_sq_three ] at * ; linarith;
    rw [ MeasureTheory.integral_sub ] <;> aesop;
    · simp_all +decide [ ← sq ];
      erw [ MeasureTheory.measureReal_def ] ; norm_num [ volume_closedBall_three ] ; ring;
      rw [ ENNReal.toReal_ofReal ( by positivity ) ] ; ring_nf ; norm_num [ hr, Real.pi_ne_zero ] ; ring_nf ; aesop;
      exact div_eq_iff ( by positivity ) |>.2 ( by ring );
    · exact ( by contrapose! left; rw [ MeasureTheory.integral_undef left ] ; positivity );
    · ring_nf;
      exact ( by contrapose! right; rw [ MeasureTheory.integral_undef right ] ; positivity );
  · rw [ MeasureTheory.integral_neg ] ; aesop;
    exact Or.inr <| integral_closedBall_coord_mul_coord_eq_zero R i j h

end RigidBody
