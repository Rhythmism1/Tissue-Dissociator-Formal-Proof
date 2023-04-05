
(* TissueDissociationMachine.v *)

Require Import ZArith.

Inductive ThermometerState := 
| Idle : ThermometerState
| Reading : ThermometerState
| Error : ThermometerState.

Inductive HeatingPadState :=
| Off : HeatingPadState
| Heating : HeatingPadState
| Overheat : HeatingPadState.

Inductive StepperMotorState :=
| Stopped : StepperMotorState
| Running : StepperMotorState
| Stuck : StepperMotorState.

Inductive SequenceState :=
| NotStarted : SequenceState
| RunningForward : nat -> SequenceState
| RunningBackward : nat -> SequenceState
| Finished : SequenceState.

Definition RPM := Z.

Record MachineState := {
  thermometerState : ThermometerState;
  heatingPadState : HeatingPadState;
  stepperMotorState : StepperMotorState;
  sequenceState : SequenceState;
}.

Definition update_thermometer (m : MachineState) : MachineState :=
match m.(thermometerState) with
| Idle => {| m with thermometerState := Reading |}
(* TissueDissociationMachine.v *)

Require Import ZArith.

Inductive ThermometerState := 
| Idle : ThermometerState
| Reading : ThermometerState
| Error : ThermometerState.

Inductive HeatingPadState :=
| Off : HeatingPadState
| Heating : HeatingPadState
| Overheat : HeatingPadState.

Inductive StepperMotorState :=
| Stopped : StepperMotorState
| Running : StepperMotorState
| Stuck : StepperMotorState.

Inductive SequenceState :=
| NotStarted : SequenceState
| RunningForward : nat -> SequenceState
| RunningBackward : nat -> SequenceState
| Finished : SequenceState.

Definition RPM := Z.

Record MachineState := {
  thermometerState : ThermometerState;
  heatingPadState : HeatingPadState;
  stepperMotorState : StepperMotorState;
  sequenceState : SequenceState;
}.

Parameter is_temperature_within_range : MachineState -> bool.

Parameter positive_rpm : RPM := 1%Z.
Parameter negative_rpm : RPM := (-1)%Z.

Parameter undefined_variable : bool := true.

Definition update_thermometer (m : MachineState) : MachineState :=
match m.(thermometerState) with
| Idle => {| m with thermometerState := Reading |}
| Reading => {| m with thermometerState := Idle |}
| Error => m
end.

Definition update_heating_pad (m : MachineState) : MachineState :=
  let overheat := negb (is_temperature_within_range m) in
  match m.(heatingPadState), overheat with
  | Off, false => {| m with heatingPadState := Heating |}
  | Heating, false => {| m with heatingPadState := Off |}
  | _, true => {| m with heatingPadState := Overheat |}
  end.

Definition update_stepper_motor (m : MachineState) (stuck : bool) : MachineState :=
match m.(stepperMotorState), stuck with
| Stopped, false => {| m with stepperMotorState := Running |}
| Running, false => {| m with stepperMotorState := Stopped |}
| _, true => {| m with stepperMotorState := Stuck |}
end.

Definition update_sequence (m : MachineState) (rpm : RPM) : MachineState :=
  match m.(sequenceState), rpm with
  | NotStarted, _ => {| m with sequenceState := RunningForward (Z.to_nat (Z.abs rpm)) |}
  | RunningForward _, positive_rpm => {| m with sequenceState := RunningBackward (Z.to_nat (Z.abs positive_rpm)) |}
  | RunningBackward _, negative_rpm => {| m with sequenceState := RunningForward (Z.to_nat (Z.abs negative_rpm)) |}
  | Finished, _ => m
  | _, _ => m  (* Invalid transitions *)
  end.

Definition valid_machine (m : MachineState) :=
  (m.(heatingPadState) <> Overheat \/ m.(thermometerState) <> Error) /\
  (m.(stepperMotorState) = Running -> (exists n, m.(sequenceState) = RunningForward n) \/ (exists n, m.(sequenceState) = RunningBackward n)).

Lemma no_overheat_on_error :
  forall (m : MachineState),
    valid_machine m ->
    valid_machine (update_heating_pad (update_thermometer m)).
Proof.
intros m [H1 H2].
unfold update_heating_pad, update_thermometer.
destruct (thermometerState m) eqn: E; simpl.

split; auto.
right; discriminate.
split; auto.
destruct (is_temperature_within_range {| thermometerState := Idle; heatingPadState := heatingPadState m;
stepperMotorState := stepperMotorState m; sequenceState := sequenceState m |}); auto.
right; discriminate.
split.
left; discriminate.
intros H; apply H2 in H.
destruct H as [[n H]|[n H]]; rewrite H; auto.
Qed.
Lemma sequence_running_on_motor_running :
forall (m : MachineState) (rpm : RPM),
valid_machine m ->
valid_machine (update_sequence (update_stepper_motor m false) rpm).
Proof.
intros m rpm [H1 H2].
unfold update_sequence, update_stepper_motor.
destruct (stepperMotorState m) eqn: E; simpl; auto.
destruct (sequenceState m) eqn: E'; simpl.

split; auto.
intros H; apply H2 in H.
rewrite E in H.
destruct H as [[n H]|[n H]]; rewrite H; auto.
destruct rpm; split; auto; try (left; exists (Z.to_nat (Z.abs (Z.pos p))); auto); try (right; exists (Z.to_nat (Z.abs (Z.neg p))); auto).
destruct rpm; split; auto; try (left; exists (Z.to_nat (Z.abs (Z.pos p))); auto); try (right; exists (Z.to_nat (Z.abs (Z.neg p))); auto).
split; auto.
intros H; apply H2 in H.
rewrite E in H.
destruct H as [[n H]|[n H]]; rewrite H; auto.
Qed.
