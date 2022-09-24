module StateMachine {
  datatype State = A | B | C
  datatype Variables = Variables(state: State, happy: bool)

  predicate AdvanceToB(v: Variables, v': Variables)
  {
    && v.state.A?
    && v' == v.(state := B)
  }

  predicate AdvanceToC(v: Variables, v': Variables)
  {
    && v.state.B?
    && v' == v.(state := C)
  }

  datatype Step =
      AdvanceToBStep
    | AdvanceToCStep

  predicate Init(v: Variables) {
    && v.state.A?
    && v.happy
  }

  predicate NextStep(v: Variables, v': Variables, step: Step) {
    match step
      case AdvanceToBStep => AdvanceToB(v, v')
      case AdvanceToCStep => AdvanceToC(v, v')
  }

  predicate Next(v: Variables, v': Variables) {
    exists step :: NextStep(v, v', step)
  }
}

module Behavior {
  import StateMachine

  // TODO: can't figure out how to solve:
  // /home/jonh/tla-liveness/liveness.dfy(40,19): Error: formal type parameter
  // 'VarType' is not used according to its variance specification (it is used
  // left of an arrow) (perhaps try declaring 'VarType' as '!VarType')
  //type VarType(!new, ==)
  //type VarType

  // TODO(jonh): try ~> --> to address the type-invariance problem?
  // https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-arrow-subset-types
  // nope.

  type VarType = StateMachine.Variables

  // We could think about replacing these function types with (total) imaps.
  type StatePred = VarType -> bool
  type ActionPred = (VarType, VarType) -> bool

  // Index type 'int' here because 'nat' causes coercions, but Dafny missed
  // some, leading to mysterious proof failures.
  type Execution = (int) -> VarType
  type TemporalPred = (Execution) -> bool


  function LiftState(statePred: StatePred) : TemporalPred
  {
    (ex:Execution) => statePred(ex(0))
  }

  function LiftAction(actionPred: ActionPred) : TemporalPred
  {
    (ex:Execution) => actionPred(ex(0), ex(1))
  }

  function Behead(ex: Execution, count: nat) : Execution
  {
    (idx: int) => ex(idx+count)
  }

  function Always(temp: TemporalPred) : TemporalPred
  {
    (ex:Execution) => forall count :: temp(Behead(ex, count))
  }

  function Not(temp: TemporalPred) : TemporalPred
  {
    (ex:Execution) => !temp(ex)
  }

  function And(tempA: TemporalPred, tempB: TemporalPred) : TemporalPred
  {
    (ex:Execution) => tempA(ex) && tempB(ex)
  }

  function Eventually(temp: TemporalPred) : TemporalPred
  {
    Not(Always(Not(temp)))
  }

  function Or(tempA: TemporalPred, tempB: TemporalPred) : TemporalPred
  {
    Not(And(Not(tempA), Not(tempB)))
  }

  function Implies(tempA: TemporalPred, tempB: TemporalPred) : TemporalPred
  {
    Or(Not(tempA), tempB)
  }

  function LeadsTo(tempA: TemporalPred, tempB: TemporalPred) : TemporalPred
  {
    Implies(tempA, Eventually(tempB))
  }

  // TODO rename to IsTautology or Valid
  predicate IsTautology(temp: TemporalPred)
  {
    forall ex :: temp(ex)
  }

  function SpecFor(init: StatePred, next: ActionPred) : TemporalPred
  {
    And(LiftState(init), Always(LiftAction(next)))
  }

  ///////////////////////////////////////////////////////////////////////////
  // Safety (induction) helpers

  // low-predicate action is always true in ex
  predicate LowAlwaysAction(ex: Execution, action: ActionPred)
  {
    // Untriggerable because Dafny avoided the matching loop!
    forall count:nat :: action(ex(count), ex(count+1))
  }

  lemma InductionToLimit(ex: Execution, next: ActionPred, inv: StatePred, limit: nat)
    requires inv(ex(0))
    requires LowAlwaysAction(ex, next)  // Always next
    requires forall v, v' :: inv(v) && next(v, v') ==> inv(v')
    ensures forall count:nat | count < limit :: inv(ex(count))
  {
    if 1 < limit {
      InductionToLimit(ex, next, inv, limit-1);
      assert next(ex(limit-2), ex((limit-2)+1));  // algebra trigger
    }
  }

  lemma Induction(ex: Execution, next: ActionPred, inv: StatePred)
    requires inv(ex(0)) // inv is established
    requires LowAlwaysAction(ex, next)  // Always next
    // inv is preserved under next
    requires forall v, v' :: inv(v) && next(v, v') ==> inv(v')
    ensures Always(LiftState(inv))(ex)
  {
    if exists idx:nat :: !inv(ex(idx)) {
      var idx:nat :| !inv(ex(idx));
      InductionToLimit(ex, next, inv, idx);
      assert next(ex(idx-1), ex(idx-1+1));  // algebra trigger for Next precondition
      assert false; // proof by contradiction
    }
  }

  // We use this to go from Always(Lift(next)) to forall i :: next
  lemma LowerAction(ex: Execution, action: ActionPred)
    requires Always(LiftAction(action))(ex)
    ensures LowAlwaysAction(ex, action)
  {
    forall count:nat ensures action(ex(count), ex(count+1)) {
      assert action(Behead(ex, count)(0), Behead(ex, count)(1));  // sequence offset trigger
    }
  }

  lemma LiftInvariant(init: StatePred, next: ActionPred, inv: StatePred)
//requires IsTautology(LiftState(init)) // these get introduced as Spec
//requires IsTautology(Always(LiftAction(next)))
    // inv is inductive under init, next
    requires forall v :: init(v) ==> inv(v)
    requires forall v, v' :: inv(v) && next(v, v') ==> inv(v') // base-level inductive statement
    ensures IsTautology(Implies(SpecFor(init, next), Always(LiftState(inv))))
  {
    // introduce a specific execution & the Implies hypothosis.
    forall ex ensures Implies(SpecFor(init, next), Always(LiftState(inv)))(ex)
    {
      if SpecFor(init, next)(ex) {
        // Use Next assumption from Spec to get execution-level induction assumption
        LowerAction(ex, next);
        Induction(ex, next, inv);
      }
    }
  }

  ///////////////////////////////////////////////////////////////////////////
  // Liveness helpers

  // If a makes b happen in the next step, then prove LeadsTo(a, b).
  lemma OneStep(next: ActionPred, before: StatePred, after: StatePred)
    requires forall v, v' | before(v) && next(v, v') :: after(v')
    ensures IsTautology(Implies(Always(LiftAction(next)), LeadsTo(LiftState(before), LiftState(after))))
  {
    assume false;
  }

  ///////////////////////////////////////////////////////////////////////////
  // Deduction rules

  lemma ModusPonens(a: TemporalPred, b: TemporalPred, c: TemporalPred)
    requires IsTautology(Implies(a, b))
    requires IsTautology(Implies(b, c))
    ensures IsTautology(Implies(a, c))
  {
    assume false;
  }

  lemma LeadsToTransitive(a: TemporalPred, b: TemporalPred, c: TemporalPred)
    requires IsTautology(LeadsTo(a, b))
    requires IsTautology(LeadsTo(b, c))
    ensures IsTautology(LeadsTo(a, c))
  {
    assume false;
  }
}

module LivenessProof {
  import opened StateMachine
  import opened Behavior

  function Spec() : TemporalPred
  {
    SpecFor(Init, Next)
  }

  lemma SpecImpliesInit()
    ensures IsTautology(Implies(Spec(), LiftState(Init)))
  {
    // Okay, that's a good sign.
  }


  lemma AlwaysHappy()
    ensures IsTautology(Implies(Spec(), Always(LiftState((v:Variables) => v.happy))))
  {
    var safety := (v:Variables) => v.happy;
    // To prove the classic Iron* safety invariant "unwinding conditions" is to prove
    // []Inv.
    LiftInvariant(Init, Next, safety);
  }

  function IsA() : StatePred { (v:Variables) => v.state.A? }
  function IsB() : StatePred { (v:Variables) => v.state.B? }
  function IsC() : StatePred { (v:Variables) => v.state.C? }

  function Goal() : TemporalPred
  {
    LeadsTo(LiftState(IsA()), LiftState(IsC()))
  }

  lemma Theorem()
    ensures IsTautology(Implies(Spec(), Goal()))
  {
    OneStep(Next, IsA(), IsB());
    assert IsTautology(Implies(Always(LiftAction(Next)), LeadsTo(LiftState(IsA()), LiftState(IsB()))));
    assert IsTautology(Implies(Spec(), Always(LiftAction(Next))));
    ModusPonens(Spec() ,Always(LiftAction(Next)), LeadsTo(LiftState(IsA()), LiftState(IsB())));
    assert IsTautology(Implies(Spec(), LeadsTo(LiftState(IsA()), LiftState(IsB()))));

    // Why doesn't this need proof!?
    OneStep(Next, IsB(), IsC());
    assert IsTautology(Implies(Spec(), LeadsTo(LiftState(IsB()), LiftState(IsC()))));

    assert IsTautology(Implies(Spec(), LeadsTo(LiftState(IsA()), LiftState(IsC())))) by {
        LeadsToTransitive(LiftState(IsA()), LiftState(IsB()), LiftState(IsC()));
    }
  }
}
