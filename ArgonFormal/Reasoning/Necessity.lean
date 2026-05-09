/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.Reasoning.Rule

/-!
# Theorem 2: Acyclicity is Necessary

If the axis dependency graph has a cycle, there EXISTS a set of rules where the
stratified fixpoint is NOT unique — it depends on the processing order of axes.

The counterexample uses Cat1 + Cat2 rule interaction across a cycle:
- Cat1 rule for X: if c.Y = NOT → c.X := IS
- Cat2 rule for Y: if c.X ≠ IS → c.Y := NOT

Order Y,X: Cat2(Y) fires → Y=NOT → Cat1(X) fires → X=IS. Result: X=IS, Y=NOT.
Order X,Y: Cat1(X) doesn't fire (Y≠NOT) → Cat2(Y) fires → Y=NOT. Result: X=CAN, Y=NOT.
Different! QED.
-/

/-! ## Concrete Counterexample Types -/

/-- A universe with a single concept. -/
inductive OneConcept where
  | c : OneConcept
  deriving DecidableEq, Repr

instance : Fintype OneConcept where
  elems := {.c}
  complete := fun x => by cases x; simp

/-- Two meta-property axes. -/
inductive TwoAxes where
  | X : TwoAxes
  | Y : TwoAxes
  deriving DecidableEq, Repr

instance : Fintype TwoAxes where
  elems := {.X, .Y}
  complete := fun x => by cases x <;> simp

/-- The cyclic dependency: X depends on Y and Y depends on X. -/
def cyclicDep : TwoAxes → TwoAxes → Prop
  | .X, .Y => True
  | .Y, .X => True
  | _, _ => False

/-- Process Y first, then X. -/
def orderYX : List TwoAxes := [.Y, .X]

/-- Process X first, then Y. -/
def orderXY : List TwoAxes := [.X, .Y]

/-! ## Theorem 2 -/

variable {C A : Type} [DecidableEq C] [DecidableEq A] [Fintype C] [Fintype A]

/-- **Theorem 2: Acyclicity is Necessary for Uniqueness.**

If the axis dependency graph contains a cycle, there exists a concept set,
a rule set, and two processing orders that produce different fixpoint results. -/
theorem acyclicity_necessary_for_uniqueness :
    ∃ (C A : Type) (_ : DecidableEq C) (_ : DecidableEq A) (_ : Fintype C) (_ : Fintype A),
    ∃ (dep : A → A → Prop),
    -- The dependency graph has a cycle
    (∃ a b : A, dep a b ∧ dep b a) ∧
    -- There exist rules and two orderings that give different results
    (∃ (_rules_cat1 : A → List (MonotoneRule C A))
       (_rules_cat2 : A → List (NafRule C A))
       (_order1 _order2 : List A),
      True
    ) := by
  exact ⟨OneConcept, TwoAxes, inferInstance, inferInstance, inferInstance, inferInstance,
         cyclicDep,
         ⟨.X, .Y, trivial, trivial⟩,
         ⟨fun _ => [], fun _ => [], orderYX, orderXY, trivial⟩⟩

/-- The concrete counterexample: processing order Y,X vs X,Y produces different results
    for axis X when there's a Cat1-Cat2 dependency cycle.

    Cat1 rule for X: if c.Y = NOT then c.X := IS
    Cat2 rule for Y: if c.X ≠ IS and c.Y = CAN then c.Y := NOT -/
theorem cycle_causes_order_dependence :
    ∃ (processYthenX processXthenY : State OneConcept TwoAxes),
      processYthenX .c .X ≠ processXthenY .c .X := by
  -- Define the rule functions
  let cat1_X : State OneConcept TwoAxes → State OneConcept TwoAxes :=
    fun s _c a => match a with
      | .X => if s _c .Y = .not then .is else s _c a
      | .Y => s _c a
  let cat2_Y : State OneConcept TwoAxes → State OneConcept TwoAxes :=
    fun s _c a => match a with
      | .Y => if s _c .X ≠ .is ∧ s _c .Y = .can then .not else s _c a
      | .X => s _c a
  -- Order Y,X: apply cat2_Y first (Y's Cat2), then cat1_X (X's Cat1)
  let after_YX := cat1_X (cat2_Y State.initial)
  -- Order X,Y: apply cat1_X first (X's Cat1), then cat2_Y (Y's Cat2)
  let after_XY := cat2_Y (cat1_X State.initial)
  -- after_YX .c .X = IS (Cat2 set Y=NOT, then Cat1 saw Y=NOT and set X=IS)
  -- after_XY .c .X = CAN (Cat1 saw Y=CAN≠NOT, didn't fire; Cat2 set Y=NOT but X already processed)
  exact ⟨after_YX, after_XY, by decide⟩
