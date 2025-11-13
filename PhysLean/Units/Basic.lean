/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Time.TimeUnit
import PhysLean.SpaceAndTime.Space.LengthUnit
import PhysLean.ClassicalMechanics.Mass.MassUnit
import PhysLean.Electromagnetism.Charge.ChargeUnit
import PhysLean.Thermodynamics.Temperature.TemperatureUnits
import PhysLean.Units.Dimension

import Mathlib.Algebra.Group.TransferInstance

/-!

# Dimensions and unit

A unit in physics arises from choice of something in physics which is non-canonical.
An example is the choice of translationally-invariant metric on the time manifold `TimeMan`.

A dimension is a property of a quantity related to how it changes with respect to a
change in the unit.

The fundamental choices one has in physics are related to:
- Time
- Length
- Mass
- Charge
- Temperature

(In fact temperature is not really a fundamental choice, however we leave this as a `TODO`.)

From these fundamental choices one can construct all other units and dimensions.

## Implementation details

Units within PhysLean are implemented with the following convention:
- The fundamental units, and the choices they correspond to, are defined within the
  appropriate physics directory, in particular:
  - `PhysLean/SpaceAndTime/Time/TimeUnit.lean`
  - `PhysLean/SpaceAndTime/Space/LengthUnit.lean`
  - `PhysLean/ClassicalMechanics/Mass/MassUnit.lean`
  - `PhysLean/Electromagnetism/Charge/ChargeUnit.lean`
  - `PhysLean/Thermodynamics/Temperature/TemperatureUnit.lean`
- In this `Units` directory, we define the necessary structures and properties
  to work derived units and dimensions.

## References

Zulip chats discussing units:
- https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/physical.20units
- https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Dimensional.20Analysis.20Revisited/with/530238303

## Note

A lot of the results around units is still experimental and should be adapted based on needs.

## Other implementations of units

There are other implementations of units in Lean, in particular:
1. https://github.com/ATOMSLab/LeanDimensionalAnalysis/tree/main
2. https://github.com/teorth/analysis/blob/main/analysis/Analysis/Misc/SI.lean
3. https://github.com/ecyrbe/lean-units
Each of these have their own advantages and specific use-cases.
For example both (1) and (3) allow for or work in Floats, allowing computability and the use
of `#eval`. This is currently not possible with the more theoretical implementation here
in PhysLean which is based exclusively on Reals.

-/

/-!

## Units

-/
open NNReal

abbrev Scaling (D : Type) [Group D] := D →* ℝ≥0ˣ

/-- The choice of units. -/
@[ext]
structure UnitChoices where
  /-- The length unit. -/
  length : LengthUnit
  /-- The time unit. -/
  time : TimeUnit
  /-- The mass unit. -/
  mass : MassUnit
  /-- The charge unit. -/
  charge : ChargeUnit
  /-- The temperature unit. -/
  temperature : TemperatureUnit

@[ext]
structure UnitScaling where
  /-- The scaling of the length unit. -/
  length : ℝ≥0ˣ
  /-- The scaling of the time unit. -/
  time : ℝ≥0ˣ
  /-- The scaling of the mass unit. -/
  mass : ℝ≥0ˣ
  /-- The scaling of the charge unit. -/
  charge : ℝ≥0ˣ
  /-- The scaling of the temperature unit. -/
  temperature : ℝ≥0ˣ

namespace UnitScaling

instance : Mul UnitScaling where
  mul s1 s2 := ⟨s1.length * s2.length,
    s1.time * s2.time,
    s1.mass * s2.mass,
    s1.charge * s2.charge,
    s1.temperature * s2.temperature⟩

@[simp] lemma mul_length (s1 s2 : UnitScaling) : (s1 * s2).length = s1.length * s2.length := rfl
@[simp] lemma mul_time (s1 s2 : UnitScaling) : (s1 * s2).time = s1.time * s2.time := rfl
@[simp] lemma mul_mass (s1 s2 : UnitScaling) : (s1 * s2).mass = s1.mass * s2.mass := rfl
@[simp] lemma mul_charge (s1 s2 : UnitScaling) : (s1 * s2).charge = s1.charge * s2.charge := rfl
@[simp] lemma mul_temperature (s1 s2 : UnitScaling) :
  (s1 * s2).temperature = s1.temperature * s2.temperature := rfl

instance : One UnitScaling where
  one := ⟨1, 1, 1, 1, 1⟩

instance : CommGroup UnitScaling where
  mul_assoc s1 s2 s3 := by
    ext1 <;> simp <;> try rw [mul_assoc]
  one_mul s := by ext1 <;> simp <;> rfl
  mul_one s := by ext1 <;> simp <;> rfl
  mul_comm s1 s2 := by ext1 <;> simp <;> rw [mul_comm]
  inv s := ⟨s.length⁻¹, s.time⁻¹, s.mass⁻¹, s.charge⁻¹, s.temperature⁻¹⟩
  inv_mul_cancel s := by ext1 <;> simp <;> rfl

lemma one_def : (1 : UnitScaling) = ⟨1, 1, 1, 1, 1⟩ := rfl

lemma mul_apply (s1 s2 : UnitScaling) :
    s1 * s2 = ⟨s1.length * s2.length,
      s1.time * s2.time,
      s1.mass * s2.mass,
      s1.charge * s2.charge,
      s1.temperature * s2.temperature⟩ := rfl

noncomputable def scaleFactor (s : UnitScaling) (d : Dimension) : ℝ :=
  s.length ^ (d.length : ℝ) *
  s.time ^ (d.time : ℝ) *
  s.mass ^ (d.mass : ℝ) *
  s.charge ^ (d.charge : ℝ) *
  s.temperature ^ (d.temperature : ℝ)

@[simp]
lemma scaleFactor_pos (s : UnitScaling) (d : Dimension) :
    0 < scaleFactor s d := by
  simp [scaleFactor, Real.rpow_pos_of_pos]

@[simp]
lemma scaleFactor_trans (s: UnitScaling) (d1 d2 : Dimension) :
    scaleFactor s (d1 * d2) = scaleFactor s d1 * scaleFactor s d2 := by
  simp only [scaleFactor, Dimension.length_mul, Rat.cast_add, Dimension.time_mul,
    Dimension.mass_mul, Dimension.charge_mul, Dimension.temperature_mul]
  repeat rw [Real.rpow_add]
  ring
  all_goals
    simp

lemma scaleFactor_trans' (s1 s2 : UnitScaling) (d : Dimension) :
    scaleFactor (s1 * s2) d = scaleFactor s1 d * scaleFactor s2 d := by
  unfold scaleFactor
  simp only [mul_apply, Units.val_mul, NNReal.coe_mul]
  repeat rw [Real.mul_rpow]
  · norm_cast
    field_simp
  all_goals simp

noncomputable def mk_unit (x : ℝ) (hx : 0 < x) : ℝ≥0ˣ :=
  Units.mk0 (⟨x, le_of_lt hx⟩ : ℝ≥0) (pos_iff_ne_zero.mp hx)

noncomputable def toScaling (s : UnitScaling) : Scaling Dimension where
  toFun d := mk_unit (scaleFactor s d) (scaleFactor_pos s d)
  map_one' := by
    simp [mk_unit, scaleFactor]
  map_mul' d1 d2 := by
    simp only [mk_unit, scaleFactor_trans]
    exact Units.val_inj.mp rfl

noncomputable def ofScaling (s : Scaling Dimension) : UnitScaling where
  length := Units.mk0 (s Dimension.L𝓭) (by simp)
  time := Units.mk0 (s Dimension.T𝓭) (by simp)
  mass := Units.mk0 (s Dimension.M𝓭) (by simp)
  charge := Units.mk0 (s Dimension.C𝓭) (by simp)
  temperature := Units.mk0 (s Dimension.Θ𝓭) (by simp)

@[simp]
lemma toScaling_mul (s1 s2 : UnitScaling) :
    toScaling (s1 * s2) = toScaling s1 * toScaling s2 := by
  ext d
  simp [toScaling, mul_apply, scaleFactor, mk_unit]
  repeat rw [Real.mul_rpow]
  · norm_cast
    field_simp
  all_goals
    simp

lemma toScaling_mul_apply (s1 s2 : UnitScaling) (d : Dimension) :
    toScaling (s1 * s2) d = toScaling s1 d * toScaling s2 d := by simp

@[simp]
lemma toScaling_one : toScaling 1 = 1 := by
  ext d
  simp [toScaling, scaleFactor, mk_unit, one_def]

@[simp]
lemma toScaling_mul_inv_cancel (s : UnitScaling) :
  toScaling s * toScaling s⁻¹ = 1 := by
  simp only [← toScaling_mul, mul_inv_cancel, toScaling_one]

lemma toScaling_inv (s : UnitScaling) :
  toScaling s⁻¹ = (toScaling s)⁻¹ := by
    have h := @inv_eq_of_mul_eq_one_right _ _ s.toScaling _ (toScaling_mul_inv_cancel s)
    simp [h]

end UnitScaling

namespace UnitChoices

def scale (u : UnitChoices) (s : UnitScaling) : UnitChoices where
  length := u.length.scale (s.length)
  time := u.time.scale (s.time)
  mass := u.mass.scale (s.mass)
  charge := u.charge.scale (s.charge)
  temperature := u.temperature.scale (s.temperature)

instance : SMul UnitScaling UnitChoices where
  smul s u := u.scale s

instance : MulAction UnitScaling UnitChoices where
  one_smul u := by
    ext <;> simp [UnitScaling.one_def, HSMul.hSMul, SMul.smul, scale]
  mul_smul s1 s2 u := by
    ext <;> simp [UnitScaling.mul_apply, HSMul.hSMul, SMul.smul, scale]

noncomputable def divide (u1 u2 : UnitChoices) : UnitScaling where
  length := Units.mk0 (u1.length / u2.length) (by simp)
  time := Units.mk0 (u1.time / u2.time) (by simp)
  mass := Units.mk0 (u1.mass / u2.mass) (by simp)
  charge := Units.mk0 (u1.charge / u2.charge) (by simp)
  temperature := Units.mk0 (u1.temperature / u2.temperature) (by simp)

noncomputable instance : HDiv UnitChoices UnitChoices UnitScaling where
  hDiv := divide

lemma div_apply (u1 u2 : UnitChoices) :
    ((u1 / u2) : UnitScaling) = ⟨
      Units.mk0 (u1.length / u2.length) (by simp),
      Units.mk0 (u1.time / u2.time) (by simp),
      Units.mk0 (u1.mass / u2.mass) (by simp),
      Units.mk0 (u1.charge / u2.charge) (by simp),
      Units.mk0 (u1.temperature / u2.temperature) (by simp)⟩ :=
  rfl

lemma div_apply_length (u1 u2 : UnitChoices) :
    (u1 / u2).length = (u1.length / u2.length : ℝ≥0) := rfl

@[simp]
lemma div_smul (u1 u2 : UnitChoices) : (u1 / u2) • u2 = u1 := by
  ext <;> simp [HDiv.hDiv, divide, HSMul.hSMul, SMul.smul, scale, Div.div, DivInvMonoid.div',
      LengthUnit.scale, TimeUnit.scale, MassUnit.scale, ChargeUnit.scale, TemperatureUnit.scale]

@[simp]
lemma smul_div (s : UnitScaling) (u : UnitChoices) :
    s • u / u = s := by
  ext
  all_goals
    simp [div_apply, HSMul.hSMul, SMul.smul, scale,
      LengthUnit.scale, TimeUnit.scale, MassUnit.scale, ChargeUnit.scale, TemperatureUnit.scale]
    simp [LengthUnit.div_eq_val, TimeUnit.div_eq_val, MassUnit.div_eq_val,
      ChargeUnit.div_eq_val, TemperatureUnit.div_eq_val]
    rfl

lemma smul_right_cancel (u : UnitChoices) (s1 s2 : UnitScaling)
    (h : s1 • u = s2 • u) : s1 = s2 := by
  rw [← smul_div s1 u, h, smul_div s2 u]

@[simp]
lemma smul_right_cancel_iff (u : UnitChoices) (s1 s2 : UnitScaling) :
    s1 • u = s2 • u ↔ s1 = s2 :=
  ⟨smul_right_cancel u s1 s2, fun h ↦ h ▸ rfl⟩

@[simp]
lemma smul_div_assoc (s : UnitScaling) (u1 u2 : UnitChoices) :
    (s • u1) / u2 = s * (u1 / u2) := by
  apply smul_right_cancel u2
  rw [div_smul, mul_smul, div_smul]

@[simp]
lemma div_self (u : UnitChoices) : u / u = (1 : UnitScaling) := by
  rw [← one_mul (u / u), ← smul_div_assoc, smul_div]

@[simp]
lemma div_mul_div_cancel (u1 u2 u3: UnitChoices) :
    (u1 / u2) * (u2 / u3) = u1 / u3 := by
  apply smul_right_cancel u3
  rw [mul_smul, div_smul, div_smul, div_smul]

@[simp]
lemma div_mul_div_cancel' (u1 u2 u3: UnitChoices) :
    (u2 / u1) * (u3 / u2) = u3 / u1 := by
  rw [mul_comm]
  simp

@[simp]
lemma inv_div_eq_div_rev (u1 u2: UnitChoices) :
    (u1 / u2)⁻¹ = (u2 / u1) := by
  rw [inv_eq_of_mul_eq_one_left]
  simp

@[simp]
lemma div_smul_eq_div_mul_inv (u1 u2: UnitChoices) (s : UnitScaling) :
    u1 / s • u2 = u1 / u2 * s⁻¹ := by
  apply smul_right_cancel (s • u2)
  conv_rhs => rw [← mul_smul]
  simp

/-- Given two choices of units `u1` and `u2` and a dimension `d`, the
  element of `ℝ≥0` corresponding to the scaling (by definition) of a quantity of dimension `d`
  when changing from units `u1` to `u2`. -/
noncomputable def dimScale (u1 u2 : UnitChoices) : Dimension →* ℝ≥0 where
  toFun d := UnitScaling.toScaling (u1 / u2) d
  map_one' := by simp
  map_mul' d1 d2 := by simp

lemma dimScale_def (u1 u2 : UnitChoices) (d : Dimension) :
    dimScale u1 u2 d =
      (u1.length / u2.length) ^ (d.length : ℝ) *
      (u1.time / u2.time) ^ (d.time : ℝ) *
      (u1.mass / u2.mass) ^ (d.mass : ℝ) *
      (u1.charge / u2.charge) ^ (d.charge : ℝ) *
      (u1.temperature / u2.temperature) ^ (d.temperature : ℝ) := rfl

lemma dimScale_apply (u1 u2 : UnitChoices) :
    dimScale u1 u2 d = UnitScaling.toScaling (u1 / u2) d := rfl

@[simp]
lemma dimScale_self (u : UnitChoices) (d : Dimension) :
    dimScale u u d = 1 := by simp [dimScale_apply]

@[simp]
lemma dimScale_one (u1 u2 : UnitChoices) :
    dimScale u1 u2 1 = 1 := by simp

lemma dimScale_transitive (u1 u2 u3 : UnitChoices) (d : Dimension) :
    dimScale u1 u2 d * dimScale u2 u3 d = dimScale u1 u3 d := by
  simp only [dimScale_apply]
  norm_cast
  rw [← UnitScaling.toScaling_mul_apply]
  simp

@[simp]
lemma dimScale_mul_symm (u1 u2 : UnitChoices) (d : Dimension) :
    dimScale u1 u2 d * dimScale u2 u1 d = 1 := by
  rw [dimScale_transitive, dimScale_self]

@[simp]
lemma dimScale_coe_mul_symm (u1 u2 : UnitChoices) (d : Dimension) :
    (toReal (dimScale u1 u2 d)) * (toReal (dimScale u2 u1 d)) = 1 := by
  norm_cast
  simp

@[simp]
lemma dimScale_neq_zero (u1 u2 : UnitChoices) (d : Dimension) :
    dimScale u1 u2 d ≠ 0 := by
  simp [dimScale_apply]

lemma dimScale_symm (u1 u2 : UnitChoices) (d : Dimension) :
    dimScale u1 u2 d = (dimScale u2 u1 d)⁻¹ := by
  rw [dimScale_apply, ← inv_div_eq_div_rev, UnitScaling.toScaling_inv]
  simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_inj]
  rfl

lemma dimScale_of_inv_eq_swap (u1 u2 : UnitChoices) (d : Dimension) :
    dimScale u1 u2 d⁻¹ = dimScale u2 u1 d := by
  simp only [map_inv]
  conv_rhs => rw [dimScale_symm]

@[simp]
lemma smul_dimScale_injective {M : Type} [MulAction ℝ≥0 M] (u1 u2 : UnitChoices) (d : Dimension)
    (m1 m2 : M) :
    (u1.dimScale u2 d) • m1 = (u1.dimScale u2 d) • m2 ↔ m1 = m2:= by
  refine IsUnit.smul_left_cancel ?_
  refine isUnit_iff_exists_inv.mpr ?_
  use u1.dimScale u2 d⁻¹
  simp

@[simp]
lemma dimScale_pos (u1 u2 : UnitChoices) (d : Dimension) :
    0 < (dimScale u1 u2 d) := by
  apply lt_of_le_of_ne
  · simp
  · exact Ne.symm (dimScale_neq_zero u1 u2 d)

TODO "LCSAY" "Make SI : UnitChoices computable, probably by
  replacing the axioms defining the units. See here:
  https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/physical.20units/near/534914807"
/-- The choice of units corresponding to SI units, that is
- meters,
- seconds,
- kilograms,
- coulombs,
- kelvin.
-/
noncomputable def SI : UnitChoices where
  length := LengthUnit.meters
  time := TimeUnit.seconds
  mass := MassUnit.kilograms
  charge := ChargeUnit.coulombs
  temperature := TemperatureUnit.kelvin

@[simp]
lemma SI_length : SI.length = LengthUnit.meters := rfl

@[simp]
lemma SI_time : SI.time = TimeUnit.seconds := rfl

@[simp]
lemma SI_mass : SI.mass = MassUnit.kilograms := rfl

@[simp]
lemma SI_charge : SI.charge = ChargeUnit.coulombs := rfl

@[simp]
lemma SI_temperature : SI.temperature = TemperatureUnit.kelvin := rfl

/-- A `UnitChoices` which is related to `SI` by a prime scaling of each
  of the underlying units. This is useful in proving that a result is not
  dimensionally correct. -/
noncomputable def SIPrimed : UnitChoices where
  length := LengthUnit.scale 2 LengthUnit.meters
  time := TimeUnit.scale 3 TimeUnit.seconds
  mass := MassUnit.scale 5 MassUnit.kilograms
  charge := ChargeUnit.scale 7 ChargeUnit.coulombs
  temperature := TemperatureUnit.scale 11 TemperatureUnit.kelvin

@[simp]
lemma dimScale_SI_SIPrimed (d : Dimension) :
    dimScale SI SIPrimed d =
      (2⁻¹ : ℝ≥0) ^ (d.length : ℝ) *
      (3⁻¹ : ℝ≥0) ^ (d.time : ℝ) *
      (5⁻¹ : ℝ≥0) ^ (d.mass : ℝ) *
      (7⁻¹ : ℝ≥0) ^ (d.charge : ℝ) *
      (11⁻¹ : ℝ≥0) ^ (d.temperature : ℝ) := by
  simp [dimScale_def, SI, SIPrimed]
  rfl

@[simp]
lemma dimScale_SIPrimed_SI (d : Dimension) :
    dimScale SIPrimed SI d =
      (2 : ℝ≥0) ^ (d.length : ℝ) *
      (3 : ℝ≥0) ^ (d.time : ℝ) *
      (5 : ℝ≥0) ^ (d.mass : ℝ) *
      (7 : ℝ≥0) ^ (d.charge : ℝ) *
      (11 : ℝ≥0) ^ (d.temperature : ℝ) := by
  simp [dimScale_def, SI, SIPrimed]
  rfl

end UnitChoices

/-!

## Types carrying dimensions

Dimensions are assigned to types with the following type-classes

- `HasDim` for any type `M` with an associated dimension
- `CarriesDimension` for a type that also has an instance of `MulAction ℝ≥0 M`

-/

/-- This typeclass indicates that there is a dimension `dim M : Dimension`
  associated with the type `M`. -/
class HasDim (M : Type) where
  /-- The dimension associated with a type `M`. -/
  d : Dimension

alias dim := HasDim.d

/-- A type `M` carries a dimension `d` if every element of `M` is supposed to have
  this dimension. For example, the type `Time` will carry a dimension `T𝓭`. -/
class abbrev CarriesDimension (M : Type) := HasDim M, MulAction ℝ≥0 M

/-!

## Terms of the current dimension

Given a type `M` which carries a dimension `d`,
we are interested in elements of `M` which depend on a choice of units, i.e. functions
`UnitChoices → M`.

We define both a proposition
- `HasDimension f` which says that `f` scales correctly with units,
and a type
- `Dimensionful M` which is the subtype of functions which `HasDimension`.

-/

/-- A quantity of type `M` which depends on a choice of units `UnitChoices` is said to be
  of dimension `d` if it scales by `UnitChoices.dimScale u1 u2 d` under a change in units. -/
def HasDimension {M : Type} [CarriesDimension M] (f : UnitChoices → M) : Prop :=
  ∀ u1 u2 : UnitChoices, f u2 = UnitChoices.dimScale u1 u2 (dim M) • f u1

lemma hasDimension_iff {M : Type} [CarriesDimension M] (f : UnitChoices → M) :
    HasDimension f ↔ ∀ u1 u2 : UnitChoices, f u2 =
    UnitChoices.dimScale u1 u2 (dim M) • f u1 := by
  rfl

/-- The subtype of functions `UnitChoices → M`, for which `M` carries a dimension,
  which `HasDimension`. -/
def Dimensionful (M : Type) [CarriesDimension M] := Subtype (HasDimension (M := M))

instance {M : Type} [CarriesDimension M] : CoeFun (Dimensionful M) (fun _ => UnitChoices → M) where
  coe := Subtype.val

@[ext]
lemma Dimensionful.ext {M : Type} [CarriesDimension M] (f1 f2 : Dimensionful M)
    (h : f1.val = f2.val) : f1 = f2 := by
  cases f1
  cases f2
  simp_all

instance {M : Type} [CarriesDimension M] : MulAction ℝ≥0 (Dimensionful M) where
  smul a f := ⟨fun u => a • f.1 u, fun u1 u2 => by
    simp only
    rw [f.2 u1 u2]
    rw [smul_comm]⟩
  one_smul f := by
    ext u
    change (1 : ℝ≥0) • f.1 u = f.1 u
    simp
  mul_smul a b f := by
    ext u
    change (a * b) • f.1 u = a • (b • f.1 u)
    rw [smul_smul]

@[simp]
lemma Dimensionful.smul_apply {M : Type} [CarriesDimension M]
    (a : ℝ≥0) (f : Dimensionful M) (u : UnitChoices) :
    (a • f).1 u = a • f.1 u := rfl

/-- For `M` carrying a dimension `d`, the equivalence between `M` and `Dimension M`,
  given a choice of units. -/
noncomputable def CarriesDimension.toDimensionful {M : Type} [CarriesDimension M]
    (u : UnitChoices) :
    M ≃ Dimensionful M where
  toFun m := {
    val := fun u1 => (u.dimScale u1 (dim M)) • m
    property := fun u1 u2 => by
      simp [smul_smul]
      rw [mul_comm, UnitChoices.dimScale_transitive]}
  invFun f := f.1 u
  left_inv m := by
    simp
  right_inv f := by
    simp only
    ext u1
    simpa using (f.2 u u1).symm

lemma CarriesDimension.toDimensionful_apply_apply
    {M : Type} [CarriesDimension M] (u1 u2 : UnitChoices) (m : M) :
    (toDimensionful u1 m).1 u2 = (u1.dimScale u2 (dim M)) • m := by rfl
